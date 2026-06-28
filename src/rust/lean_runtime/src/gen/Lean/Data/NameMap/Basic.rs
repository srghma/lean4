// Lean compiler output
// Module: Lean.Data.NameMap.Basic
// Imports: Std.Data.HashSet.Basic Std.Data.TreeSet.Basic Lean.Data.SSet Lean.Data.Name
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Repr::{
    l_List_repr___redArg, l_Prod_repr___boxed, l_Repr_addAppParen,
    l_instReprTupleOfRepr___redArg___lam__0,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec___boxed;
use crate::r#gen::Init::Prelude::{l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed};
use crate::r#gen::Lean::Data::Name::{
    initialize_Lean_Data_Name, l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl,
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, l_Lean_Name_isPrefixOf,
    l_Lean_Name_isSuffixOf, runtime_initialize_Lean_Data_Name,
};
use crate::r#gen::Lean::Data::SMap::{
    l_Lean_SMap_contains___redArg, l_Lean_SMap_empty, l_Lean_SMap_insert___redArg,
};
use crate::r#gen::Lean::Data::SSet::{
    initialize_Lean_Data_SSet, runtime_initialize_Lean_Data_SSet,
};
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::l_Std_DHashMap_Internal_AssocList_length___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Balancing::l_Std_DTreeMap_Internal_Impl_balance___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_erase___redArg, l_Std_DTreeMap_Internal_Impl_link___redArg,
    l_Std_DTreeMap_Internal_Impl_link2___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::{
    l_Std_DTreeMap_Internal_Impl_foldl___redArg, l_Std_DTreeMap_Internal_Impl_foldrM___redArg,
    l_Std_DTreeMap_Internal_Impl_forInStep___redArg,
};
use crate::r#gen::Std::Data::HashSet::Basic::{
    initialize_Std_Data_HashSet_Basic, runtime_initialize_Std_Data_HashSet_Basic,
};
use crate::r#gen::Std::Data::TreeSet::Basic::{
    initialize_Std_Data_TreeSet_Basic, l_Std_TreeSet_ofArray___redArg,
    l_Std_TreeSet_ofList___redArg, runtime_initialize_Std_Data_TreeSet_Basic,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_uint64_of_nat,
    lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint64,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_NameMap_instRepr___aux__1___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_NameMap_instRepr___aux__1___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_NameMap_instRepr___aux__1___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_NameMap_instRepr___aux__1___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_reprPrec___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_NameMap_instRepr___aux__1___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_NameMap_instRepr___aux__1___redArg___closed__2_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            83, 116, 100, 46, 84, 114, 101, 101, 77, 97, 112, 46, 111, 102, 76, 105, 115, 116, 32,
            0,
        ],
    };
static mut l_Lean_NameMap_instRepr___aux__1___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_NameMap_instRepr___aux__1___redArg___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_NameMap_instRepr___aux__1___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_NameMap_instRepr___aux__1___redArg___closed__4_value: LeanClosureObject<0> =
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
static mut l_Lean_NameMap_instRepr___aux__1___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_NameMap_instRepr___aux__1___redArg___closed__5_value: LeanClosureObject<0> =
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
static mut l_Lean_NameMap_instRepr___aux__1___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_NameMap_instRepr___aux__1___redArg___closed__6_value: LeanClosureObject<0> =
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
static mut l_Lean_NameMap_instRepr___aux__1___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_NameMap_instRepr___aux__1___redArg___closed__7_value: LeanClosureObject<0> =
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
static mut l_Lean_NameMap_instRepr___aux__1___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_NameMap_instRepr___aux__1___redArg___closed__8_value: LeanClosureObject<0> =
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
static mut l_Lean_NameMap_instRepr___aux__1___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_NameMap_instRepr___aux__1___redArg___closed__9_value: LeanClosureObject<0> =
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
static mut l_Lean_NameMap_instRepr___aux__1___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_NameMap_instRepr___aux__1___redArg___closed__10_value: LeanClosureObject<0> =
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
static mut l_Lean_NameMap_instRepr___aux__1___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_NameMap_instRepr___aux__1___redArg___closed__11_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_NameMap_instRepr___aux__1___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_NameMap_instRepr___aux__1___redArg___closed__12_value: LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__11_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_NameMap_instRepr___aux__1___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_NameMap_instRepr___aux__1___redArg___closed__13_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_NameMap_instRepr___aux__1___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameMap_instRepr___aux__1___redArg___closed__13_value)
        as *mut LeanObject;
pub static mut l_Lean_NameSet_empty: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_NameSet_instEmptyCollection: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_NameSet_instInhabited: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_NameSet_instAppend___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_NameSet_append as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_NameSet_instAppend___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameSet_instAppend___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_NameSet_instAppend: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameSet_instAppend___closed__0_value) as *mut LeanObject;
pub static l_Lean_NameSet_instSingletonName___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_NameSet_instSingletonName___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_NameSet_instSingletonName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameSet_instSingletonName___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_NameSet_instSingletonName: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameSet_instSingletonName___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_NameSet_instUnion: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameSet_instAppend___closed__0_value) as *mut LeanObject;
pub static l_Lean_NameSet_instInter___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_NameSet_instInter___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_NameSet_instInter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameSet_instInter___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_NameSet_instInter: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameSet_instInter___closed__0_value) as *mut LeanObject;
pub static l_Lean_NameSet_instSDiff___lam__1___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_NameSet_instSDiff___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameSet_instSDiff___lam__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_NameSet_instSDiff___lam__1___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_NameSet_instSDiff___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_NameSet_instSDiff___lam__1___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_NameSet_instSDiff___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameSet_instSDiff___lam__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_NameSet_instSDiff___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_NameSet_instSDiff___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_NameSet_instSDiff___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameSet_instSDiff___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_NameSet_instSDiff: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameSet_instSDiff___closed__0_value) as *mut LeanObject;
pub static l_Lean_NameSSet_empty___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_NameSSet_empty___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameSSet_empty___closed__0_value) as *mut LeanObject;
pub static l_Lean_NameSSet_empty___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_NameSSet_empty___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameSSet_empty___closed__1_value) as *mut LeanObject;
static mut l_Lean_NameSSet_empty___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_NameSSet_empty___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_NameSSet_empty: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_NameSSet_instEmptyCollection: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_NameSSet_instInhabited: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_NameHashSet_empty___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_NameHashSet_empty___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_NameHashSet_empty___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_NameHashSet_empty___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_NameHashSet_empty: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_NameHashSet_instEmptyCollection: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_NameHashSet_instInhabited: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0: u64 = 0;
pub unsafe fn l_Lean_mkNameMap(mut v_00_u03b1_1061_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    v___x_1062_ = lean_box(1);
    return v___x_1062_;
}
pub unsafe fn l_Lean_NameMap_instRepr___aux__1___redArg___lam__0(
    mut v_x1_1063_: *mut LeanObject,
    mut v_x2_1064_: *mut LeanObject,
    mut v_x3_1065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    v___x_1066_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1066_, 0, v_x1_1063_);
    lean_ctor_set(v___x_1066_, 1, v_x2_1064_);
    v___x_1067_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1067_, 0, v___x_1066_);
    lean_ctor_set(v___x_1067_, 1, v_x3_1065_);
    return v___x_1067_;
}
pub unsafe fn l_Lean_NameMap_instRepr___aux__1___redArg(
    mut v_inst_1092_: *mut LeanObject,
    mut v_m_1093_: *mut LeanObject,
    mut v_prec_1094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    v___f_1095_ = l_Lean_NameMap_instRepr___aux__1___redArg___closed__0;
    v___x_1096_ = l_Lean_NameMap_instRepr___aux__1___redArg___closed__1;
    v___x_1097_ = l_Lean_NameMap_instRepr___aux__1___redArg___closed__3;
    v___f_1098_ = lean_alloc_closure(
        l_instReprTupleOfRepr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1098_, 0, v_inst_1092_);
    v___x_1099_ = lean_alloc_closure(l_Prod_repr___boxed as *mut core::ffi::c_void, 6, 4);
    lean_closure_set(v___x_1099_, 0, lean_box(0));
    lean_closure_set(v___x_1099_, 1, lean_box(0));
    lean_closure_set(v___x_1099_, 2, v___x_1096_);
    lean_closure_set(v___x_1099_, 3, v___f_1098_);
    v___x_1100_ = lean_box(0);
    v___x_1101_ = l_Lean_NameMap_instRepr___aux__1___redArg___closed__13;
    v___x_1102_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_1101_,
        v___f_1095_,
        v___x_1100_,
        v_m_1093_,
    );
    v___x_1103_ = l_List_repr___redArg(v___x_1099_, v___x_1102_);
    v___x_1104_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1104_, 0, v___x_1097_);
    lean_ctor_set(v___x_1104_, 1, v___x_1103_);
    v___x_1105_ = l_Repr_addAppParen(v___x_1104_, v_prec_1094_);
    return v___x_1105_;
}
pub unsafe fn l_Lean_NameMap_instRepr___aux__1___redArg___boxed(
    mut v_inst_1106_: *mut LeanObject,
    mut v_m_1107_: *mut LeanObject,
    mut v_prec_1108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1109_: *mut LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_Lean_NameMap_instRepr___aux__1___redArg(v_inst_1106_, v_m_1107_, v_prec_1108_);
    lean_dec(v_prec_1108_);
    return v_res_1109_;
}
pub unsafe fn l_Lean_NameMap_instRepr___aux__1(
    mut v_00_u03b1_1110_: *mut LeanObject,
    mut v_inst_1111_: *mut LeanObject,
    mut v_m_1112_: *mut LeanObject,
    mut v_prec_1113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    v___f_1114_ = l_Lean_NameMap_instRepr___aux__1___redArg___closed__0;
    v___x_1115_ = l_Lean_NameMap_instRepr___aux__1___redArg___closed__1;
    v___x_1116_ = l_Lean_NameMap_instRepr___aux__1___redArg___closed__3;
    v___f_1117_ = lean_alloc_closure(
        l_instReprTupleOfRepr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1117_, 0, v_inst_1111_);
    v___x_1118_ = lean_alloc_closure(l_Prod_repr___boxed as *mut core::ffi::c_void, 6, 4);
    lean_closure_set(v___x_1118_, 0, lean_box(0));
    lean_closure_set(v___x_1118_, 1, lean_box(0));
    lean_closure_set(v___x_1118_, 2, v___x_1115_);
    lean_closure_set(v___x_1118_, 3, v___f_1117_);
    v___x_1119_ = lean_box(0);
    v___x_1120_ = l_Lean_NameMap_instRepr___aux__1___redArg___closed__13;
    v___x_1121_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_1120_,
        v___f_1114_,
        v___x_1119_,
        v_m_1112_,
    );
    v___x_1122_ = l_List_repr___redArg(v___x_1118_, v___x_1121_);
    v___x_1123_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1123_, 0, v___x_1116_);
    lean_ctor_set(v___x_1123_, 1, v___x_1122_);
    v___x_1124_ = l_Repr_addAppParen(v___x_1123_, v_prec_1113_);
    return v___x_1124_;
}
pub unsafe fn l_Lean_NameMap_instRepr___aux__1___boxed(
    mut v_00_u03b1_1125_: *mut LeanObject,
    mut v_inst_1126_: *mut LeanObject,
    mut v_m_1127_: *mut LeanObject,
    mut v_prec_1128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1129_: *mut LeanObject = core::ptr::null_mut();
    v_res_1129_ =
        l_Lean_NameMap_instRepr___aux__1(v_00_u03b1_1125_, v_inst_1126_, v_m_1127_, v_prec_1128_);
    lean_dec(v_prec_1128_);
    return v_res_1129_;
}
pub unsafe fn l_Lean_NameMap_instRepr___redArg(
    mut v_inst_1130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    v___x_1131_ = lean_alloc_closure(
        l_Lean_NameMap_instRepr___aux__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_1131_, 0, lean_box(0));
    lean_closure_set(v___x_1131_, 1, v_inst_1130_);
    return v___x_1131_;
}
pub unsafe fn l_Lean_NameMap_instRepr(
    mut v_00_u03b1_1132_: *mut LeanObject,
    mut v_inst_1133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    v___x_1134_ = lean_alloc_closure(
        l_Lean_NameMap_instRepr___aux__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_1134_, 0, lean_box(0));
    lean_closure_set(v___x_1134_, 1, v_inst_1133_);
    return v___x_1134_;
}
pub unsafe fn l_Lean_NameMap_instEmptyCollection(
    mut v_00_u03b1_1135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    v___x_1136_ = lean_box(1);
    return v___x_1136_;
}
pub unsafe fn l_Lean_NameMap_instInhabited(
    mut v_00_u03b1_1137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    v___x_1138_ = lean_box(1);
    return v___x_1138_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
    mut v_k_1139_: *mut LeanObject,
    mut v_v_1140_: *mut LeanObject,
    mut v_t_1141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1149_: u8 = 0;
    let mut v___x_1150_: u8 = 0;
    let mut v_impl_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: u8 = 0;
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1169_: u8 = 0;
    let mut v_size_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: u8 = 0;
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1181_: u8 = 0;
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1207_: u8 = 0;
    let mut v_unused_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1221_: u8 = 0;
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1225_: u8 = 0;
    let mut v_unused_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1232_: u8 = 0;
    let mut v_unused_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1244_: u8 = 0;
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1252_: u8 = 0;
    let mut v_unused_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1260_: u8 = 0;
    let mut v_k_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1265_: u8 = 0;
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1276_: u8 = 0;
    let mut v_unused_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1280_: u8 = 0;
    let mut v_unused_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: u8 = 0;
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1309_: u8 = 0;
    let mut v_size_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: u8 = 0;
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1321_: u8 = 0;
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1346_: u8 = 0;
    let mut v_unused_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1359_: u8 = 0;
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut v_unused_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1370_: u8 = 0;
    let mut v_unused_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1382_: u8 = 0;
    let mut v_k_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1387_: u8 = 0;
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1398_: u8 = 0;
    let mut v_unused_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1402_: u8 = 0;
    let mut v_unused_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1410_: u8 = 0;
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1418_: u8 = 0;
    let mut v_unused_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1426_: u8 = 0;
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1141_) == 0 {
                    v_size_1142_ = lean_ctor_get(v_t_1141_, 0);
                    v_k_1143_ = lean_ctor_get(v_t_1141_, 1);
                    v_v_1144_ = lean_ctor_get(v_t_1141_, 2);
                    v_l_1145_ = lean_ctor_get(v_t_1141_, 3);
                    v_r_1146_ = lean_ctor_get(v_t_1141_, 4);
                    v_isSharedCheck_1426_ = (!lean_is_exclusive(v_t_1141_)) as u8;
                    if v_isSharedCheck_1426_ == 0 {
                        v___x_1148_ = v_t_1141_;
                        v_isShared_1149_ = v_isSharedCheck_1426_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_1146_);
                        lean_inc(v_l_1145_);
                        lean_inc(v_v_1144_);
                        lean_inc(v_k_1143_);
                        lean_inc(v_size_1142_);
                        lean_dec(v_t_1141_);
                        v___x_1148_ = lean_box(0);
                        v_isShared_1149_ = v_isSharedCheck_1426_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1427_ = lean_unsigned_to_nat(1);
                    v___x_1428_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_1428_, 0, v___x_1427_);
                    lean_ctor_set(v___x_1428_, 1, v_k_1139_);
                    lean_ctor_set(v___x_1428_, 2, v_v_1140_);
                    lean_ctor_set(v___x_1428_, 3, v_t_1141_);
                    lean_ctor_set(v___x_1428_, 4, v_t_1141_);
                    return v___x_1428_;
                }
            }
            1 => {
                v___x_1150_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1139_, v_k_1143_);
                match v___x_1150_ {
                    0 => {
                        lean_dec(v_size_1142_);
                        v_impl_1151_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1139_, v_v_1140_, v_l_1145_);
                        v___x_1152_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_r_1146_) == 0 {
                            v_size_1153_ = lean_ctor_get(v_r_1146_, 0);
                            v_size_1154_ = lean_ctor_get(v_impl_1151_, 0);
                            lean_inc(v_size_1154_);
                            v_k_1155_ = lean_ctor_get(v_impl_1151_, 1);
                            lean_inc(v_k_1155_);
                            v_v_1156_ = lean_ctor_get(v_impl_1151_, 2);
                            lean_inc(v_v_1156_);
                            v_l_1157_ = lean_ctor_get(v_impl_1151_, 3);
                            lean_inc(v_l_1157_);
                            v_r_1158_ = lean_ctor_get(v_impl_1151_, 4);
                            lean_inc(v_r_1158_);
                            v___x_1159_ = lean_unsigned_to_nat(3);
                            v___x_1160_ = lean_nat_mul(v___x_1159_, v_size_1153_);
                            v___x_1161_ = lean_nat_dec_lt(v___x_1160_, v_size_1154_);
                            lean_dec(v___x_1160_);
                            if v___x_1161_ == 0 {
                                lean_dec(v_r_1158_);
                                lean_dec(v_l_1157_);
                                lean_dec(v_v_1156_);
                                lean_dec(v_k_1155_);
                                v___x_1162_ = lean_nat_add(v___x_1152_, v_size_1154_);
                                lean_dec(v_size_1154_);
                                v___x_1163_ = lean_nat_add(v___x_1162_, v_size_1153_);
                                lean_dec(v___x_1162_);
                                if v_isShared_1149_ == 0 {
                                    lean_ctor_set(v___x_1148_, 3, v_impl_1151_);
                                    lean_ctor_set(v___x_1148_, 0, v___x_1163_);
                                    v___x_1165_ = v___x_1148_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
                                    lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_k_1143_);
                                    lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_v_1144_);
                                    lean_ctor_set(v_reuseFailAlloc_1166_, 3, v_impl_1151_);
                                    lean_ctor_set(v_reuseFailAlloc_1166_, 4, v_r_1146_);
                                    v___x_1165_ = v_reuseFailAlloc_1166_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1232_ = (!lean_is_exclusive(v_impl_1151_)) as u8;
                                if v_isSharedCheck_1232_ == 0 {
                                    v_unused_1233_ = lean_ctor_get(v_impl_1151_, 4);
                                    lean_dec(v_unused_1233_);
                                    v_unused_1234_ = lean_ctor_get(v_impl_1151_, 3);
                                    lean_dec(v_unused_1234_);
                                    v_unused_1235_ = lean_ctor_get(v_impl_1151_, 2);
                                    lean_dec(v_unused_1235_);
                                    v_unused_1236_ = lean_ctor_get(v_impl_1151_, 1);
                                    lean_dec(v_unused_1236_);
                                    v_unused_1237_ = lean_ctor_get(v_impl_1151_, 0);
                                    lean_dec(v_unused_1237_);
                                    v___x_1168_ = v_impl_1151_;
                                    v_isShared_1169_ = v_isSharedCheck_1232_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_impl_1151_);
                                    v___x_1168_ = lean_box(0);
                                    v_isShared_1169_ = v_isSharedCheck_1232_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1238_ = lean_ctor_get(v_impl_1151_, 3);
                            lean_inc(v_l_1238_);
                            if lean_obj_tag(v_l_1238_) == 0 {
                                v_r_1239_ = lean_ctor_get(v_impl_1151_, 4);
                                v_k_1240_ = lean_ctor_get(v_impl_1151_, 1);
                                v_v_1241_ = lean_ctor_get(v_impl_1151_, 2);
                                v_isSharedCheck_1252_ = (!lean_is_exclusive(v_impl_1151_)) as u8;
                                if v_isSharedCheck_1252_ == 0 {
                                    v_unused_1253_ = lean_ctor_get(v_impl_1151_, 3);
                                    lean_dec(v_unused_1253_);
                                    v_unused_1254_ = lean_ctor_get(v_impl_1151_, 0);
                                    lean_dec(v_unused_1254_);
                                    v___x_1243_ = v_impl_1151_;
                                    v_isShared_1244_ = v_isSharedCheck_1252_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_r_1239_);
                                    lean_inc(v_v_1241_);
                                    lean_inc(v_k_1240_);
                                    lean_dec(v_impl_1151_);
                                    v___x_1243_ = lean_box(0);
                                    v_isShared_1244_ = v_isSharedCheck_1252_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_1255_ = lean_ctor_get(v_impl_1151_, 4);
                                lean_inc(v_r_1255_);
                                if lean_obj_tag(v_r_1255_) == 0 {
                                    v_k_1256_ = lean_ctor_get(v_impl_1151_, 1);
                                    v_v_1257_ = lean_ctor_get(v_impl_1151_, 2);
                                    v_isSharedCheck_1280_ =
                                        (!lean_is_exclusive(v_impl_1151_)) as u8;
                                    if v_isSharedCheck_1280_ == 0 {
                                        v_unused_1281_ = lean_ctor_get(v_impl_1151_, 4);
                                        lean_dec(v_unused_1281_);
                                        v_unused_1282_ = lean_ctor_get(v_impl_1151_, 3);
                                        lean_dec(v_unused_1282_);
                                        v_unused_1283_ = lean_ctor_get(v_impl_1151_, 0);
                                        lean_dec(v_unused_1283_);
                                        v___x_1259_ = v_impl_1151_;
                                        v_isShared_1260_ = v_isSharedCheck_1280_;
                                        state = 16;
                                        continue;
                                    } else {
                                        lean_inc(v_v_1257_);
                                        lean_inc(v_k_1256_);
                                        lean_dec(v_impl_1151_);
                                        v___x_1259_ = lean_box(0);
                                        v_isShared_1260_ = v_isSharedCheck_1280_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_1284_ = lean_unsigned_to_nat(2);
                                    if v_isShared_1149_ == 0 {
                                        lean_ctor_set(v___x_1148_, 4, v_r_1255_);
                                        lean_ctor_set(v___x_1148_, 3, v_impl_1151_);
                                        lean_ctor_set(v___x_1148_, 0, v___x_1284_);
                                        v___x_1286_ = v___x_1148_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
                                        lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_k_1143_);
                                        lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_v_1144_);
                                        lean_ctor_set(v_reuseFailAlloc_1287_, 3, v_impl_1151_);
                                        lean_ctor_set(v_reuseFailAlloc_1287_, 4, v_r_1255_);
                                        v___x_1286_ = v_reuseFailAlloc_1287_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        lean_dec(v_v_1144_);
                        lean_dec(v_k_1143_);
                        if v_isShared_1149_ == 0 {
                            lean_ctor_set(v___x_1148_, 2, v_v_1140_);
                            lean_ctor_set(v___x_1148_, 1, v_k_1139_);
                            v___x_1289_ = v___x_1148_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_size_1142_);
                            lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_k_1139_);
                            lean_ctor_set(v_reuseFailAlloc_1290_, 2, v_v_1140_);
                            lean_ctor_set(v_reuseFailAlloc_1290_, 3, v_l_1145_);
                            lean_ctor_set(v_reuseFailAlloc_1290_, 4, v_r_1146_);
                            v___x_1289_ = v_reuseFailAlloc_1290_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec(v_size_1142_);
                        v_impl_1291_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1139_, v_v_1140_, v_r_1146_);
                        v___x_1292_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_l_1145_) == 0 {
                            v_size_1293_ = lean_ctor_get(v_l_1145_, 0);
                            v_size_1294_ = lean_ctor_get(v_impl_1291_, 0);
                            lean_inc(v_size_1294_);
                            v_k_1295_ = lean_ctor_get(v_impl_1291_, 1);
                            lean_inc(v_k_1295_);
                            v_v_1296_ = lean_ctor_get(v_impl_1291_, 2);
                            lean_inc(v_v_1296_);
                            v_l_1297_ = lean_ctor_get(v_impl_1291_, 3);
                            lean_inc(v_l_1297_);
                            v_r_1298_ = lean_ctor_get(v_impl_1291_, 4);
                            lean_inc(v_r_1298_);
                            v___x_1299_ = lean_unsigned_to_nat(3);
                            v___x_1300_ = lean_nat_mul(v___x_1299_, v_size_1293_);
                            v___x_1301_ = lean_nat_dec_lt(v___x_1300_, v_size_1294_);
                            lean_dec(v___x_1300_);
                            if v___x_1301_ == 0 {
                                lean_dec(v_r_1298_);
                                lean_dec(v_l_1297_);
                                lean_dec(v_v_1296_);
                                lean_dec(v_k_1295_);
                                v___x_1302_ = lean_nat_add(v___x_1292_, v_size_1293_);
                                v___x_1303_ = lean_nat_add(v___x_1302_, v_size_1294_);
                                lean_dec(v_size_1294_);
                                lean_dec(v___x_1302_);
                                if v_isShared_1149_ == 0 {
                                    lean_ctor_set(v___x_1148_, 4, v_impl_1291_);
                                    lean_ctor_set(v___x_1148_, 0, v___x_1303_);
                                    v___x_1305_ = v___x_1148_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
                                    lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_k_1143_);
                                    lean_ctor_set(v_reuseFailAlloc_1306_, 2, v_v_1144_);
                                    lean_ctor_set(v_reuseFailAlloc_1306_, 3, v_l_1145_);
                                    lean_ctor_set(v_reuseFailAlloc_1306_, 4, v_impl_1291_);
                                    v___x_1305_ = v_reuseFailAlloc_1306_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1370_ = (!lean_is_exclusive(v_impl_1291_)) as u8;
                                if v_isSharedCheck_1370_ == 0 {
                                    v_unused_1371_ = lean_ctor_get(v_impl_1291_, 4);
                                    lean_dec(v_unused_1371_);
                                    v_unused_1372_ = lean_ctor_get(v_impl_1291_, 3);
                                    lean_dec(v_unused_1372_);
                                    v_unused_1373_ = lean_ctor_get(v_impl_1291_, 2);
                                    lean_dec(v_unused_1373_);
                                    v_unused_1374_ = lean_ctor_get(v_impl_1291_, 1);
                                    lean_dec(v_unused_1374_);
                                    v_unused_1375_ = lean_ctor_get(v_impl_1291_, 0);
                                    lean_dec(v_unused_1375_);
                                    v___x_1308_ = v_impl_1291_;
                                    v_isShared_1309_ = v_isSharedCheck_1370_;
                                    state = 24;
                                    continue;
                                } else {
                                    lean_dec(v_impl_1291_);
                                    v___x_1308_ = lean_box(0);
                                    v_isShared_1309_ = v_isSharedCheck_1370_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1376_ = lean_ctor_get(v_impl_1291_, 3);
                            lean_inc(v_l_1376_);
                            if lean_obj_tag(v_l_1376_) == 0 {
                                v_r_1377_ = lean_ctor_get(v_impl_1291_, 4);
                                v_k_1378_ = lean_ctor_get(v_impl_1291_, 1);
                                v_v_1379_ = lean_ctor_get(v_impl_1291_, 2);
                                v_isSharedCheck_1402_ = (!lean_is_exclusive(v_impl_1291_)) as u8;
                                if v_isSharedCheck_1402_ == 0 {
                                    v_unused_1403_ = lean_ctor_get(v_impl_1291_, 3);
                                    lean_dec(v_unused_1403_);
                                    v_unused_1404_ = lean_ctor_get(v_impl_1291_, 0);
                                    lean_dec(v_unused_1404_);
                                    v___x_1381_ = v_impl_1291_;
                                    v_isShared_1382_ = v_isSharedCheck_1402_;
                                    state = 34;
                                    continue;
                                } else {
                                    lean_inc(v_r_1377_);
                                    lean_inc(v_v_1379_);
                                    lean_inc(v_k_1378_);
                                    lean_dec(v_impl_1291_);
                                    v___x_1381_ = lean_box(0);
                                    v_isShared_1382_ = v_isSharedCheck_1402_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_1405_ = lean_ctor_get(v_impl_1291_, 4);
                                lean_inc(v_r_1405_);
                                if lean_obj_tag(v_r_1405_) == 0 {
                                    v_k_1406_ = lean_ctor_get(v_impl_1291_, 1);
                                    v_v_1407_ = lean_ctor_get(v_impl_1291_, 2);
                                    v_isSharedCheck_1418_ =
                                        (!lean_is_exclusive(v_impl_1291_)) as u8;
                                    if v_isSharedCheck_1418_ == 0 {
                                        v_unused_1419_ = lean_ctor_get(v_impl_1291_, 4);
                                        lean_dec(v_unused_1419_);
                                        v_unused_1420_ = lean_ctor_get(v_impl_1291_, 3);
                                        lean_dec(v_unused_1420_);
                                        v_unused_1421_ = lean_ctor_get(v_impl_1291_, 0);
                                        lean_dec(v_unused_1421_);
                                        v___x_1409_ = v_impl_1291_;
                                        v_isShared_1410_ = v_isSharedCheck_1418_;
                                        state = 39;
                                        continue;
                                    } else {
                                        lean_inc(v_v_1407_);
                                        lean_inc(v_k_1406_);
                                        lean_dec(v_impl_1291_);
                                        v___x_1409_ = lean_box(0);
                                        v_isShared_1410_ = v_isSharedCheck_1418_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_1422_ = lean_unsigned_to_nat(2);
                                    if v_isShared_1149_ == 0 {
                                        lean_ctor_set(v___x_1148_, 4, v_impl_1291_);
                                        lean_ctor_set(v___x_1148_, 3, v_r_1405_);
                                        lean_ctor_set(v___x_1148_, 0, v___x_1422_);
                                        v___x_1424_ = v___x_1148_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
                                        lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_k_1143_);
                                        lean_ctor_set(v_reuseFailAlloc_1425_, 2, v_v_1144_);
                                        lean_ctor_set(v_reuseFailAlloc_1425_, 3, v_r_1405_);
                                        lean_ctor_set(v_reuseFailAlloc_1425_, 4, v_impl_1291_);
                                        v___x_1424_ = v_reuseFailAlloc_1425_;
                                        state = 42;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1165_;
            }
            3 => {
                v_size_1170_ = lean_ctor_get(v_l_1157_, 0);
                v_size_1171_ = lean_ctor_get(v_r_1158_, 0);
                v_k_1172_ = lean_ctor_get(v_r_1158_, 1);
                v_v_1173_ = lean_ctor_get(v_r_1158_, 2);
                v_l_1174_ = lean_ctor_get(v_r_1158_, 3);
                v_r_1175_ = lean_ctor_get(v_r_1158_, 4);
                v___x_1176_ = lean_unsigned_to_nat(2);
                v___x_1177_ = lean_nat_mul(v___x_1176_, v_size_1170_);
                v___x_1178_ = lean_nat_dec_lt(v_size_1171_, v___x_1177_);
                lean_dec(v___x_1177_);
                if v___x_1178_ == 0 {
                    lean_inc(v_r_1175_);
                    lean_inc(v_l_1174_);
                    lean_inc(v_v_1173_);
                    lean_inc(v_k_1172_);
                    v_isSharedCheck_1207_ = (!lean_is_exclusive(v_r_1158_)) as u8;
                    if v_isSharedCheck_1207_ == 0 {
                        v_unused_1208_ = lean_ctor_get(v_r_1158_, 4);
                        lean_dec(v_unused_1208_);
                        v_unused_1209_ = lean_ctor_get(v_r_1158_, 3);
                        lean_dec(v_unused_1209_);
                        v_unused_1210_ = lean_ctor_get(v_r_1158_, 2);
                        lean_dec(v_unused_1210_);
                        v_unused_1211_ = lean_ctor_get(v_r_1158_, 1);
                        lean_dec(v_unused_1211_);
                        v_unused_1212_ = lean_ctor_get(v_r_1158_, 0);
                        lean_dec(v_unused_1212_);
                        v___x_1180_ = v_r_1158_;
                        v_isShared_1181_ = v_isSharedCheck_1207_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_r_1158_);
                        v___x_1180_ = lean_box(0);
                        v_isShared_1181_ = v_isSharedCheck_1207_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1148_);
                    v___x_1213_ = lean_nat_add(v___x_1152_, v_size_1154_);
                    lean_dec(v_size_1154_);
                    v___x_1214_ = lean_nat_add(v___x_1213_, v_size_1153_);
                    lean_dec(v___x_1213_);
                    v___x_1215_ = lean_nat_add(v___x_1152_, v_size_1153_);
                    v___x_1216_ = lean_nat_add(v___x_1215_, v_size_1171_);
                    lean_dec(v___x_1215_);
                    lean_inc_ref(v_r_1146_);
                    if v_isShared_1169_ == 0 {
                        lean_ctor_set(v___x_1168_, 4, v_r_1146_);
                        lean_ctor_set(v___x_1168_, 3, v_r_1158_);
                        lean_ctor_set(v___x_1168_, 2, v_v_1144_);
                        lean_ctor_set(v___x_1168_, 1, v_k_1143_);
                        lean_ctor_set(v___x_1168_, 0, v___x_1216_);
                        v___x_1218_ = v___x_1168_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1216_);
                        lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_k_1143_);
                        lean_ctor_set(v_reuseFailAlloc_1231_, 2, v_v_1144_);
                        lean_ctor_set(v_reuseFailAlloc_1231_, 3, v_r_1158_);
                        lean_ctor_set(v_reuseFailAlloc_1231_, 4, v_r_1146_);
                        v___x_1218_ = v_reuseFailAlloc_1231_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1182_ = lean_nat_add(v___x_1152_, v_size_1154_);
                lean_dec(v_size_1154_);
                v___x_1183_ = lean_nat_add(v___x_1182_, v_size_1153_);
                lean_dec(v___x_1182_);
                v___x_1195_ = lean_nat_add(v___x_1152_, v_size_1170_);
                if lean_obj_tag(v_l_1174_) == 0 {
                    v_size_1205_ = lean_ctor_get(v_l_1174_, 0);
                    lean_inc(v_size_1205_);
                    v___y_1197_ = v_size_1205_;
                    state = 8;
                    continue;
                } else {
                    v___x_1206_ = lean_unsigned_to_nat(0);
                    v___y_1197_ = v___x_1206_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1188_ = lean_nat_add(v___y_1186_, v___y_1187_);
                lean_dec(v___y_1187_);
                lean_dec(v___y_1186_);
                if v_isShared_1181_ == 0 {
                    lean_ctor_set(v___x_1180_, 4, v_r_1146_);
                    lean_ctor_set(v___x_1180_, 3, v_r_1175_);
                    lean_ctor_set(v___x_1180_, 2, v_v_1144_);
                    lean_ctor_set(v___x_1180_, 1, v_k_1143_);
                    lean_ctor_set(v___x_1180_, 0, v___x_1188_);
                    v___x_1190_ = v___x_1180_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1188_);
                    lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_k_1143_);
                    lean_ctor_set(v_reuseFailAlloc_1194_, 2, v_v_1144_);
                    lean_ctor_set(v_reuseFailAlloc_1194_, 3, v_r_1175_);
                    lean_ctor_set(v_reuseFailAlloc_1194_, 4, v_r_1146_);
                    v___x_1190_ = v_reuseFailAlloc_1194_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1169_ == 0 {
                    lean_ctor_set(v___x_1168_, 4, v___x_1190_);
                    lean_ctor_set(v___x_1168_, 3, v___y_1185_);
                    lean_ctor_set(v___x_1168_, 2, v_v_1173_);
                    lean_ctor_set(v___x_1168_, 1, v_k_1172_);
                    lean_ctor_set(v___x_1168_, 0, v___x_1183_);
                    v___x_1192_ = v___x_1168_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1183_);
                    lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_k_1172_);
                    lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_v_1173_);
                    lean_ctor_set(v_reuseFailAlloc_1193_, 3, v___y_1185_);
                    lean_ctor_set(v_reuseFailAlloc_1193_, 4, v___x_1190_);
                    v___x_1192_ = v_reuseFailAlloc_1193_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1192_;
            }
            8 => {
                v___x_1198_ = lean_nat_add(v___x_1195_, v___y_1197_);
                lean_dec(v___y_1197_);
                lean_dec(v___x_1195_);
                if v_isShared_1149_ == 0 {
                    lean_ctor_set(v___x_1148_, 4, v_l_1174_);
                    lean_ctor_set(v___x_1148_, 3, v_l_1157_);
                    lean_ctor_set(v___x_1148_, 2, v_v_1156_);
                    lean_ctor_set(v___x_1148_, 1, v_k_1155_);
                    lean_ctor_set(v___x_1148_, 0, v___x_1198_);
                    v___x_1200_ = v___x_1148_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1198_);
                    lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_k_1155_);
                    lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_v_1156_);
                    lean_ctor_set(v_reuseFailAlloc_1204_, 3, v_l_1157_);
                    lean_ctor_set(v_reuseFailAlloc_1204_, 4, v_l_1174_);
                    v___x_1200_ = v_reuseFailAlloc_1204_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1201_ = lean_nat_add(v___x_1152_, v_size_1153_);
                if lean_obj_tag(v_r_1175_) == 0 {
                    v_size_1202_ = lean_ctor_get(v_r_1175_, 0);
                    lean_inc(v_size_1202_);
                    v___y_1185_ = v___x_1200_;
                    v___y_1186_ = v___x_1201_;
                    v___y_1187_ = v_size_1202_;
                    state = 5;
                    continue;
                } else {
                    v___x_1203_ = lean_unsigned_to_nat(0);
                    v___y_1185_ = v___x_1200_;
                    v___y_1186_ = v___x_1201_;
                    v___y_1187_ = v___x_1203_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1225_ = (!lean_is_exclusive(v_r_1146_)) as u8;
                if v_isSharedCheck_1225_ == 0 {
                    v_unused_1226_ = lean_ctor_get(v_r_1146_, 4);
                    lean_dec(v_unused_1226_);
                    v_unused_1227_ = lean_ctor_get(v_r_1146_, 3);
                    lean_dec(v_unused_1227_);
                    v_unused_1228_ = lean_ctor_get(v_r_1146_, 2);
                    lean_dec(v_unused_1228_);
                    v_unused_1229_ = lean_ctor_get(v_r_1146_, 1);
                    lean_dec(v_unused_1229_);
                    v_unused_1230_ = lean_ctor_get(v_r_1146_, 0);
                    lean_dec(v_unused_1230_);
                    v___x_1220_ = v_r_1146_;
                    v_isShared_1221_ = v_isSharedCheck_1225_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_r_1146_);
                    v___x_1220_ = lean_box(0);
                    v_isShared_1221_ = v_isSharedCheck_1225_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1221_ == 0 {
                    lean_ctor_set(v___x_1220_, 4, v___x_1218_);
                    lean_ctor_set(v___x_1220_, 3, v_l_1157_);
                    lean_ctor_set(v___x_1220_, 2, v_v_1156_);
                    lean_ctor_set(v___x_1220_, 1, v_k_1155_);
                    lean_ctor_set(v___x_1220_, 0, v___x_1214_);
                    v___x_1223_ = v___x_1220_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1214_);
                    lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_k_1155_);
                    lean_ctor_set(v_reuseFailAlloc_1224_, 2, v_v_1156_);
                    lean_ctor_set(v_reuseFailAlloc_1224_, 3, v_l_1157_);
                    lean_ctor_set(v_reuseFailAlloc_1224_, 4, v___x_1218_);
                    v___x_1223_ = v_reuseFailAlloc_1224_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1223_;
            }
            13 => {
                v___x_1245_ = lean_unsigned_to_nat(3);
                lean_inc(v_r_1239_);
                if v_isShared_1244_ == 0 {
                    lean_ctor_set(v___x_1243_, 3, v_r_1239_);
                    lean_ctor_set(v___x_1243_, 2, v_v_1144_);
                    lean_ctor_set(v___x_1243_, 1, v_k_1143_);
                    lean_ctor_set(v___x_1243_, 0, v___x_1152_);
                    v___x_1247_ = v___x_1243_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1152_);
                    lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_k_1143_);
                    lean_ctor_set(v_reuseFailAlloc_1251_, 2, v_v_1144_);
                    lean_ctor_set(v_reuseFailAlloc_1251_, 3, v_r_1239_);
                    lean_ctor_set(v_reuseFailAlloc_1251_, 4, v_r_1239_);
                    v___x_1247_ = v_reuseFailAlloc_1251_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_1149_ == 0 {
                    lean_ctor_set(v___x_1148_, 4, v___x_1247_);
                    lean_ctor_set(v___x_1148_, 3, v_l_1238_);
                    lean_ctor_set(v___x_1148_, 2, v_v_1241_);
                    lean_ctor_set(v___x_1148_, 1, v_k_1240_);
                    lean_ctor_set(v___x_1148_, 0, v___x_1245_);
                    v___x_1249_ = v___x_1148_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1245_);
                    lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_k_1240_);
                    lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_v_1241_);
                    lean_ctor_set(v_reuseFailAlloc_1250_, 3, v_l_1238_);
                    lean_ctor_set(v_reuseFailAlloc_1250_, 4, v___x_1247_);
                    v___x_1249_ = v_reuseFailAlloc_1250_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1249_;
            }
            16 => {
                v_k_1261_ = lean_ctor_get(v_r_1255_, 1);
                v_v_1262_ = lean_ctor_get(v_r_1255_, 2);
                v_isSharedCheck_1276_ = (!lean_is_exclusive(v_r_1255_)) as u8;
                if v_isSharedCheck_1276_ == 0 {
                    v_unused_1277_ = lean_ctor_get(v_r_1255_, 4);
                    lean_dec(v_unused_1277_);
                    v_unused_1278_ = lean_ctor_get(v_r_1255_, 3);
                    lean_dec(v_unused_1278_);
                    v_unused_1279_ = lean_ctor_get(v_r_1255_, 0);
                    lean_dec(v_unused_1279_);
                    v___x_1264_ = v_r_1255_;
                    v_isShared_1265_ = v_isSharedCheck_1276_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_v_1262_);
                    lean_inc(v_k_1261_);
                    lean_dec(v_r_1255_);
                    v___x_1264_ = lean_box(0);
                    v_isShared_1265_ = v_isSharedCheck_1276_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_1266_ = lean_unsigned_to_nat(3);
                if v_isShared_1265_ == 0 {
                    lean_ctor_set(v___x_1264_, 4, v_l_1238_);
                    lean_ctor_set(v___x_1264_, 3, v_l_1238_);
                    lean_ctor_set(v___x_1264_, 2, v_v_1257_);
                    lean_ctor_set(v___x_1264_, 1, v_k_1256_);
                    lean_ctor_set(v___x_1264_, 0, v___x_1152_);
                    v___x_1268_ = v___x_1264_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1152_);
                    lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_k_1256_);
                    lean_ctor_set(v_reuseFailAlloc_1275_, 2, v_v_1257_);
                    lean_ctor_set(v_reuseFailAlloc_1275_, 3, v_l_1238_);
                    lean_ctor_set(v_reuseFailAlloc_1275_, 4, v_l_1238_);
                    v___x_1268_ = v_reuseFailAlloc_1275_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_1260_ == 0 {
                    lean_ctor_set(v___x_1259_, 4, v_l_1238_);
                    lean_ctor_set(v___x_1259_, 2, v_v_1144_);
                    lean_ctor_set(v___x_1259_, 1, v_k_1143_);
                    lean_ctor_set(v___x_1259_, 0, v___x_1152_);
                    v___x_1270_ = v___x_1259_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1152_);
                    lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_k_1143_);
                    lean_ctor_set(v_reuseFailAlloc_1274_, 2, v_v_1144_);
                    lean_ctor_set(v_reuseFailAlloc_1274_, 3, v_l_1238_);
                    lean_ctor_set(v_reuseFailAlloc_1274_, 4, v_l_1238_);
                    v___x_1270_ = v_reuseFailAlloc_1274_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1149_ == 0 {
                    lean_ctor_set(v___x_1148_, 4, v___x_1270_);
                    lean_ctor_set(v___x_1148_, 3, v___x_1268_);
                    lean_ctor_set(v___x_1148_, 2, v_v_1262_);
                    lean_ctor_set(v___x_1148_, 1, v_k_1261_);
                    lean_ctor_set(v___x_1148_, 0, v___x_1266_);
                    v___x_1272_ = v___x_1148_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1266_);
                    lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_k_1261_);
                    lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_v_1262_);
                    lean_ctor_set(v_reuseFailAlloc_1273_, 3, v___x_1268_);
                    lean_ctor_set(v_reuseFailAlloc_1273_, 4, v___x_1270_);
                    v___x_1272_ = v_reuseFailAlloc_1273_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1272_;
            }
            21 => {
                return v___x_1286_;
            }
            22 => {
                return v___x_1289_;
            }
            23 => {
                return v___x_1305_;
            }
            24 => {
                v_size_1310_ = lean_ctor_get(v_l_1297_, 0);
                v_k_1311_ = lean_ctor_get(v_l_1297_, 1);
                v_v_1312_ = lean_ctor_get(v_l_1297_, 2);
                v_l_1313_ = lean_ctor_get(v_l_1297_, 3);
                v_r_1314_ = lean_ctor_get(v_l_1297_, 4);
                v_size_1315_ = lean_ctor_get(v_r_1298_, 0);
                v___x_1316_ = lean_unsigned_to_nat(2);
                v___x_1317_ = lean_nat_mul(v___x_1316_, v_size_1315_);
                v___x_1318_ = lean_nat_dec_lt(v_size_1310_, v___x_1317_);
                lean_dec(v___x_1317_);
                if v___x_1318_ == 0 {
                    lean_inc(v_r_1314_);
                    lean_inc(v_l_1313_);
                    lean_inc(v_v_1312_);
                    lean_inc(v_k_1311_);
                    v_isSharedCheck_1346_ = (!lean_is_exclusive(v_l_1297_)) as u8;
                    if v_isSharedCheck_1346_ == 0 {
                        v_unused_1347_ = lean_ctor_get(v_l_1297_, 4);
                        lean_dec(v_unused_1347_);
                        v_unused_1348_ = lean_ctor_get(v_l_1297_, 3);
                        lean_dec(v_unused_1348_);
                        v_unused_1349_ = lean_ctor_get(v_l_1297_, 2);
                        lean_dec(v_unused_1349_);
                        v_unused_1350_ = lean_ctor_get(v_l_1297_, 1);
                        lean_dec(v_unused_1350_);
                        v_unused_1351_ = lean_ctor_get(v_l_1297_, 0);
                        lean_dec(v_unused_1351_);
                        v___x_1320_ = v_l_1297_;
                        v_isShared_1321_ = v_isSharedCheck_1346_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_l_1297_);
                        v___x_1320_ = lean_box(0);
                        v_isShared_1321_ = v_isSharedCheck_1346_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1148_);
                    v___x_1352_ = lean_nat_add(v___x_1292_, v_size_1293_);
                    v___x_1353_ = lean_nat_add(v___x_1352_, v_size_1294_);
                    lean_dec(v_size_1294_);
                    v___x_1354_ = lean_nat_add(v___x_1352_, v_size_1310_);
                    lean_dec(v___x_1352_);
                    lean_inc_ref(v_l_1145_);
                    if v_isShared_1309_ == 0 {
                        lean_ctor_set(v___x_1308_, 4, v_l_1297_);
                        lean_ctor_set(v___x_1308_, 3, v_l_1145_);
                        lean_ctor_set(v___x_1308_, 2, v_v_1144_);
                        lean_ctor_set(v___x_1308_, 1, v_k_1143_);
                        lean_ctor_set(v___x_1308_, 0, v___x_1354_);
                        v___x_1356_ = v___x_1308_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1354_);
                        lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_k_1143_);
                        lean_ctor_set(v_reuseFailAlloc_1369_, 2, v_v_1144_);
                        lean_ctor_set(v_reuseFailAlloc_1369_, 3, v_l_1145_);
                        lean_ctor_set(v_reuseFailAlloc_1369_, 4, v_l_1297_);
                        v___x_1356_ = v_reuseFailAlloc_1369_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_1322_ = lean_nat_add(v___x_1292_, v_size_1293_);
                v___x_1323_ = lean_nat_add(v___x_1322_, v_size_1294_);
                lean_dec(v_size_1294_);
                if lean_obj_tag(v_l_1313_) == 0 {
                    v_size_1344_ = lean_ctor_get(v_l_1313_, 0);
                    lean_inc(v_size_1344_);
                    v___y_1336_ = v_size_1344_;
                    state = 29;
                    continue;
                } else {
                    v___x_1345_ = lean_unsigned_to_nat(0);
                    v___y_1336_ = v___x_1345_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_1328_ = lean_nat_add(v___y_1326_, v___y_1327_);
                lean_dec(v___y_1327_);
                lean_dec(v___y_1326_);
                if v_isShared_1321_ == 0 {
                    lean_ctor_set(v___x_1320_, 4, v_r_1298_);
                    lean_ctor_set(v___x_1320_, 3, v_r_1314_);
                    lean_ctor_set(v___x_1320_, 2, v_v_1296_);
                    lean_ctor_set(v___x_1320_, 1, v_k_1295_);
                    lean_ctor_set(v___x_1320_, 0, v___x_1328_);
                    v___x_1330_ = v___x_1320_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1328_);
                    lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_k_1295_);
                    lean_ctor_set(v_reuseFailAlloc_1334_, 2, v_v_1296_);
                    lean_ctor_set(v_reuseFailAlloc_1334_, 3, v_r_1314_);
                    lean_ctor_set(v_reuseFailAlloc_1334_, 4, v_r_1298_);
                    v___x_1330_ = v_reuseFailAlloc_1334_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_1309_ == 0 {
                    lean_ctor_set(v___x_1308_, 4, v___x_1330_);
                    lean_ctor_set(v___x_1308_, 3, v___y_1325_);
                    lean_ctor_set(v___x_1308_, 2, v_v_1312_);
                    lean_ctor_set(v___x_1308_, 1, v_k_1311_);
                    lean_ctor_set(v___x_1308_, 0, v___x_1323_);
                    v___x_1332_ = v___x_1308_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1323_);
                    lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_k_1311_);
                    lean_ctor_set(v_reuseFailAlloc_1333_, 2, v_v_1312_);
                    lean_ctor_set(v_reuseFailAlloc_1333_, 3, v___y_1325_);
                    lean_ctor_set(v_reuseFailAlloc_1333_, 4, v___x_1330_);
                    v___x_1332_ = v_reuseFailAlloc_1333_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1332_;
            }
            29 => {
                v___x_1337_ = lean_nat_add(v___x_1322_, v___y_1336_);
                lean_dec(v___y_1336_);
                lean_dec(v___x_1322_);
                if v_isShared_1149_ == 0 {
                    lean_ctor_set(v___x_1148_, 4, v_l_1313_);
                    lean_ctor_set(v___x_1148_, 0, v___x_1337_);
                    v___x_1339_ = v___x_1148_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1337_);
                    lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_k_1143_);
                    lean_ctor_set(v_reuseFailAlloc_1343_, 2, v_v_1144_);
                    lean_ctor_set(v_reuseFailAlloc_1343_, 3, v_l_1145_);
                    lean_ctor_set(v_reuseFailAlloc_1343_, 4, v_l_1313_);
                    v___x_1339_ = v_reuseFailAlloc_1343_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_1340_ = lean_nat_add(v___x_1292_, v_size_1315_);
                if lean_obj_tag(v_r_1314_) == 0 {
                    v_size_1341_ = lean_ctor_get(v_r_1314_, 0);
                    lean_inc(v_size_1341_);
                    v___y_1325_ = v___x_1339_;
                    v___y_1326_ = v___x_1340_;
                    v___y_1327_ = v_size_1341_;
                    state = 26;
                    continue;
                } else {
                    v___x_1342_ = lean_unsigned_to_nat(0);
                    v___y_1325_ = v___x_1339_;
                    v___y_1326_ = v___x_1340_;
                    v___y_1327_ = v___x_1342_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_1363_ = (!lean_is_exclusive(v_l_1145_)) as u8;
                if v_isSharedCheck_1363_ == 0 {
                    v_unused_1364_ = lean_ctor_get(v_l_1145_, 4);
                    lean_dec(v_unused_1364_);
                    v_unused_1365_ = lean_ctor_get(v_l_1145_, 3);
                    lean_dec(v_unused_1365_);
                    v_unused_1366_ = lean_ctor_get(v_l_1145_, 2);
                    lean_dec(v_unused_1366_);
                    v_unused_1367_ = lean_ctor_get(v_l_1145_, 1);
                    lean_dec(v_unused_1367_);
                    v_unused_1368_ = lean_ctor_get(v_l_1145_, 0);
                    lean_dec(v_unused_1368_);
                    v___x_1358_ = v_l_1145_;
                    v_isShared_1359_ = v_isSharedCheck_1363_;
                    state = 32;
                    continue;
                } else {
                    lean_dec(v_l_1145_);
                    v___x_1358_ = lean_box(0);
                    v_isShared_1359_ = v_isSharedCheck_1363_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1359_ == 0 {
                    lean_ctor_set(v___x_1358_, 4, v_r_1298_);
                    lean_ctor_set(v___x_1358_, 3, v___x_1356_);
                    lean_ctor_set(v___x_1358_, 2, v_v_1296_);
                    lean_ctor_set(v___x_1358_, 1, v_k_1295_);
                    lean_ctor_set(v___x_1358_, 0, v___x_1353_);
                    v___x_1361_ = v___x_1358_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1353_);
                    lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_k_1295_);
                    lean_ctor_set(v_reuseFailAlloc_1362_, 2, v_v_1296_);
                    lean_ctor_set(v_reuseFailAlloc_1362_, 3, v___x_1356_);
                    lean_ctor_set(v_reuseFailAlloc_1362_, 4, v_r_1298_);
                    v___x_1361_ = v_reuseFailAlloc_1362_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1361_;
            }
            34 => {
                v_k_1383_ = lean_ctor_get(v_l_1376_, 1);
                v_v_1384_ = lean_ctor_get(v_l_1376_, 2);
                v_isSharedCheck_1398_ = (!lean_is_exclusive(v_l_1376_)) as u8;
                if v_isSharedCheck_1398_ == 0 {
                    v_unused_1399_ = lean_ctor_get(v_l_1376_, 4);
                    lean_dec(v_unused_1399_);
                    v_unused_1400_ = lean_ctor_get(v_l_1376_, 3);
                    lean_dec(v_unused_1400_);
                    v_unused_1401_ = lean_ctor_get(v_l_1376_, 0);
                    lean_dec(v_unused_1401_);
                    v___x_1386_ = v_l_1376_;
                    v_isShared_1387_ = v_isSharedCheck_1398_;
                    state = 35;
                    continue;
                } else {
                    lean_inc(v_v_1384_);
                    lean_inc(v_k_1383_);
                    lean_dec(v_l_1376_);
                    v___x_1386_ = lean_box(0);
                    v_isShared_1387_ = v_isSharedCheck_1398_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_1388_ = lean_unsigned_to_nat(3);
                lean_inc_n(v_r_1377_, 2);
                if v_isShared_1387_ == 0 {
                    lean_ctor_set(v___x_1386_, 4, v_r_1377_);
                    lean_ctor_set(v___x_1386_, 3, v_r_1377_);
                    lean_ctor_set(v___x_1386_, 2, v_v_1144_);
                    lean_ctor_set(v___x_1386_, 1, v_k_1143_);
                    lean_ctor_set(v___x_1386_, 0, v___x_1292_);
                    v___x_1390_ = v___x_1386_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1292_);
                    lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_k_1143_);
                    lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_v_1144_);
                    lean_ctor_set(v_reuseFailAlloc_1397_, 3, v_r_1377_);
                    lean_ctor_set(v_reuseFailAlloc_1397_, 4, v_r_1377_);
                    v___x_1390_ = v_reuseFailAlloc_1397_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                lean_inc(v_r_1377_);
                if v_isShared_1382_ == 0 {
                    lean_ctor_set(v___x_1381_, 3, v_r_1377_);
                    lean_ctor_set(v___x_1381_, 0, v___x_1292_);
                    v___x_1392_ = v___x_1381_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1292_);
                    lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_k_1378_);
                    lean_ctor_set(v_reuseFailAlloc_1396_, 2, v_v_1379_);
                    lean_ctor_set(v_reuseFailAlloc_1396_, 3, v_r_1377_);
                    lean_ctor_set(v_reuseFailAlloc_1396_, 4, v_r_1377_);
                    v___x_1392_ = v_reuseFailAlloc_1396_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_1149_ == 0 {
                    lean_ctor_set(v___x_1148_, 4, v___x_1392_);
                    lean_ctor_set(v___x_1148_, 3, v___x_1390_);
                    lean_ctor_set(v___x_1148_, 2, v_v_1384_);
                    lean_ctor_set(v___x_1148_, 1, v_k_1383_);
                    lean_ctor_set(v___x_1148_, 0, v___x_1388_);
                    v___x_1394_ = v___x_1148_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1388_);
                    lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_k_1383_);
                    lean_ctor_set(v_reuseFailAlloc_1395_, 2, v_v_1384_);
                    lean_ctor_set(v_reuseFailAlloc_1395_, 3, v___x_1390_);
                    lean_ctor_set(v_reuseFailAlloc_1395_, 4, v___x_1392_);
                    v___x_1394_ = v_reuseFailAlloc_1395_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_1394_;
            }
            39 => {
                v___x_1411_ = lean_unsigned_to_nat(3);
                if v_isShared_1410_ == 0 {
                    lean_ctor_set(v___x_1409_, 4, v_l_1376_);
                    lean_ctor_set(v___x_1409_, 2, v_v_1144_);
                    lean_ctor_set(v___x_1409_, 1, v_k_1143_);
                    lean_ctor_set(v___x_1409_, 0, v___x_1292_);
                    v___x_1413_ = v___x_1409_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1292_);
                    lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_k_1143_);
                    lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_v_1144_);
                    lean_ctor_set(v_reuseFailAlloc_1417_, 3, v_l_1376_);
                    lean_ctor_set(v_reuseFailAlloc_1417_, 4, v_l_1376_);
                    v___x_1413_ = v_reuseFailAlloc_1417_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_1149_ == 0 {
                    lean_ctor_set(v___x_1148_, 4, v_r_1405_);
                    lean_ctor_set(v___x_1148_, 3, v___x_1413_);
                    lean_ctor_set(v___x_1148_, 2, v_v_1407_);
                    lean_ctor_set(v___x_1148_, 1, v_k_1406_);
                    lean_ctor_set(v___x_1148_, 0, v___x_1411_);
                    v___x_1415_ = v___x_1148_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1411_);
                    lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_k_1406_);
                    lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_v_1407_);
                    lean_ctor_set(v_reuseFailAlloc_1416_, 3, v___x_1413_);
                    lean_ctor_set(v_reuseFailAlloc_1416_, 4, v_r_1405_);
                    v___x_1415_ = v_reuseFailAlloc_1416_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_1415_;
            }
            42 => {
                return v___x_1424_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_NameMap_insert___redArg(
    mut v_m_1429_: *mut LeanObject,
    mut v_n_1430_: *mut LeanObject,
    mut v_a_1431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    v___x_1432_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_n_1430_, v_a_1431_, v_m_1429_,
    );
    return v___x_1432_;
}
pub unsafe fn l_Lean_NameMap_insert(
    mut v_00_u03b1_1433_: *mut LeanObject,
    mut v_m_1434_: *mut LeanObject,
    mut v_n_1435_: *mut LeanObject,
    mut v_a_1436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    v___x_1437_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_n_1435_, v_a_1436_, v_m_1434_,
    );
    return v___x_1437_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0(
    mut v_00_u03b2_1438_: *mut LeanObject,
    mut v_k_1439_: *mut LeanObject,
    mut v_v_1440_: *mut LeanObject,
    mut v_t_1441_: *mut LeanObject,
    mut v_hl_1442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    v___x_1443_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_k_1439_, v_v_1440_, v_t_1441_,
    );
    return v___x_1443_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(
    mut v_k_1444_: *mut LeanObject,
    mut v_t_1445_: *mut LeanObject,
) -> u8 {
    let mut v_k_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u8 = 0;
    let mut v___x_1451_: u8 = 0;
    let mut v___x_1453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1445_) == 0 {
                    v_k_1446_ = lean_ctor_get(v_t_1445_, 1);
                    v_l_1447_ = lean_ctor_get(v_t_1445_, 3);
                    v_r_1448_ = lean_ctor_get(v_t_1445_, 4);
                    v___x_1449_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1444_, v_k_1446_);
                    match v___x_1449_ {
                        0 => {
                            v_t_1445_ = v_l_1447_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_1451_ = 1;
                            return v___x_1451_;
                        }
                        _ => {
                            v_t_1445_ = v_r_1448_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1453_ = 0;
                    return v___x_1453_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg___boxed(
    mut v_k_1454_: *mut LeanObject,
    mut v_t_1455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1456_: u8 = 0;
    let mut v_r_1457_: *mut LeanObject = core::ptr::null_mut();
    v_res_1456_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(
            v_k_1454_, v_t_1455_,
        );
    lean_dec(v_t_1455_);
    lean_dec(v_k_1454_);
    v_r_1457_ = lean_box((v_res_1456_) as usize);
    return v_r_1457_;
}
pub unsafe fn l_Lean_NameMap_contains___redArg(
    mut v_m_1458_: *mut LeanObject,
    mut v_n_1459_: *mut LeanObject,
) -> u8 {
    let mut v___x_1460_: u8 = 0;
    v___x_1460_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(
            v_n_1459_, v_m_1458_,
        );
    return v___x_1460_;
}
pub unsafe fn l_Lean_NameMap_contains___redArg___boxed(
    mut v_m_1461_: *mut LeanObject,
    mut v_n_1462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1463_: u8 = 0;
    let mut v_r_1464_: *mut LeanObject = core::ptr::null_mut();
    v_res_1463_ = l_Lean_NameMap_contains___redArg(v_m_1461_, v_n_1462_);
    lean_dec(v_n_1462_);
    lean_dec(v_m_1461_);
    v_r_1464_ = lean_box((v_res_1463_) as usize);
    return v_r_1464_;
}
pub unsafe fn l_Lean_NameMap_contains(
    mut v_00_u03b1_1465_: *mut LeanObject,
    mut v_m_1466_: *mut LeanObject,
    mut v_n_1467_: *mut LeanObject,
) -> u8 {
    let mut v___x_1468_: u8 = 0;
    v___x_1468_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(
            v_n_1467_, v_m_1466_,
        );
    return v___x_1468_;
}
pub unsafe fn l_Lean_NameMap_contains___boxed(
    mut v_00_u03b1_1469_: *mut LeanObject,
    mut v_m_1470_: *mut LeanObject,
    mut v_n_1471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1472_: u8 = 0;
    let mut v_r_1473_: *mut LeanObject = core::ptr::null_mut();
    v_res_1472_ = l_Lean_NameMap_contains(v_00_u03b1_1469_, v_m_1470_, v_n_1471_);
    lean_dec(v_n_1471_);
    lean_dec(v_m_1470_);
    v_r_1473_ = lean_box((v_res_1472_) as usize);
    return v_r_1473_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0(
    mut v_00_u03b2_1474_: *mut LeanObject,
    mut v_k_1475_: *mut LeanObject,
    mut v_t_1476_: *mut LeanObject,
) -> u8 {
    let mut v___x_1477_: u8 = 0;
    v___x_1477_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(
            v_k_1475_, v_t_1476_,
        );
    return v___x_1477_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___boxed(
    mut v_00_u03b2_1478_: *mut LeanObject,
    mut v_k_1479_: *mut LeanObject,
    mut v_t_1480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1481_: u8 = 0;
    let mut v_r_1482_: *mut LeanObject = core::ptr::null_mut();
    v_res_1481_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0(
        v_00_u03b2_1478_,
        v_k_1479_,
        v_t_1480_,
    );
    lean_dec(v_t_1480_);
    lean_dec(v_k_1479_);
    v_r_1482_ = lean_box((v_res_1481_) as usize);
    return v_r_1482_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
    mut v_t_1483_: *mut LeanObject,
    mut v_k_1484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: u8 = 0;
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1483_) == 0 {
                    v_k_1485_ = lean_ctor_get(v_t_1483_, 1);
                    v_v_1486_ = lean_ctor_get(v_t_1483_, 2);
                    v_l_1487_ = lean_ctor_get(v_t_1483_, 3);
                    v_r_1488_ = lean_ctor_get(v_t_1483_, 4);
                    v___x_1489_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1484_, v_k_1485_);
                    match v___x_1489_ {
                        0 => {
                            v_t_1483_ = v_l_1487_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_inc(v_v_1486_);
                            v___x_1491_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_1491_, 0, v_v_1486_);
                            return v___x_1491_;
                        }
                        _ => {
                            v_t_1483_ = v_r_1488_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1493_ = lean_box(0);
                    return v___x_1493_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg___boxed(
    mut v_t_1494_: *mut LeanObject,
    mut v_k_1495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1496_: *mut LeanObject = core::ptr::null_mut();
    v_res_1496_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_t_1494_, v_k_1495_,
        );
    lean_dec(v_k_1495_);
    lean_dec(v_t_1494_);
    return v_res_1496_;
}
pub unsafe fn l_Lean_NameMap_find_x3f___redArg(
    mut v_m_1497_: *mut LeanObject,
    mut v_n_1498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    v___x_1499_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_m_1497_, v_n_1498_,
        );
    return v___x_1499_;
}
pub unsafe fn l_Lean_NameMap_find_x3f___redArg___boxed(
    mut v_m_1500_: *mut LeanObject,
    mut v_n_1501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1502_: *mut LeanObject = core::ptr::null_mut();
    v_res_1502_ = l_Lean_NameMap_find_x3f___redArg(v_m_1500_, v_n_1501_);
    lean_dec(v_n_1501_);
    lean_dec(v_m_1500_);
    return v_res_1502_;
}
pub unsafe fn l_Lean_NameMap_find_x3f(
    mut v_00_u03b1_1503_: *mut LeanObject,
    mut v_m_1504_: *mut LeanObject,
    mut v_n_1505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    v___x_1506_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_m_1504_, v_n_1505_,
        );
    return v___x_1506_;
}
pub unsafe fn l_Lean_NameMap_find_x3f___boxed(
    mut v_00_u03b1_1507_: *mut LeanObject,
    mut v_m_1508_: *mut LeanObject,
    mut v_n_1509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1510_: *mut LeanObject = core::ptr::null_mut();
    v_res_1510_ = l_Lean_NameMap_find_x3f(v_00_u03b1_1507_, v_m_1508_, v_n_1509_);
    lean_dec(v_n_1509_);
    lean_dec(v_m_1508_);
    return v_res_1510_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0(
    mut v_00_u03b4_1511_: *mut LeanObject,
    mut v_t_1512_: *mut LeanObject,
    mut v_k_1513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    v___x_1514_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_t_1512_, v_k_1513_,
        );
    return v___x_1514_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___boxed(
    mut v_00_u03b4_1515_: *mut LeanObject,
    mut v_t_1516_: *mut LeanObject,
    mut v_k_1517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1518_: *mut LeanObject = core::ptr::null_mut();
    v_res_1518_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0(
        v_00_u03b4_1515_,
        v_t_1516_,
        v_k_1517_,
    );
    lean_dec(v_k_1517_);
    lean_dec(v_t_1516_);
    return v_res_1518_;
}
pub unsafe fn l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__0(
    mut v_f_1519_: *mut LeanObject,
    mut v_a_1520_: *mut LeanObject,
    mut v_b_1521_: *mut LeanObject,
    mut v_c_1522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    v___x_1523_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1523_, 0, v_a_1520_);
    lean_ctor_set(v___x_1523_, 1, v_b_1521_);
    v___x_1524_ = lean_apply_2(v_f_1519_, v___x_1523_, v_c_1522_);
    return v___x_1524_;
}
pub unsafe fn l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1(
    mut v_toPure_1525_: *mut LeanObject,
    mut v_____do__lift_1526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    v_a_1527_ = lean_ctor_get(v_____do__lift_1526_, 0);
    lean_inc(v_a_1527_);
    lean_dec_ref(v_____do__lift_1526_);
    v___x_1528_ = lean_apply_2(v_toPure_1525_, lean_box(0), v_a_1527_);
    return v___x_1528_;
}
pub unsafe fn l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg(
    mut v_inst_1529_: *mut LeanObject,
    mut v_m_1530_: *mut LeanObject,
    mut v_init_1531_: *mut LeanObject,
    mut v_f_1532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1533_ = lean_ctor_get(v_inst_1529_, 0);
    v_toBind_1534_ = lean_ctor_get(v_inst_1529_, 1);
    lean_inc(v_toBind_1534_);
    v_toPure_1535_ = lean_ctor_get(v_toApplicative_1533_, 1);
    lean_inc(v_toPure_1535_);
    v___f_1536_ = lean_alloc_closure(
        l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1536_, 0, v_f_1532_);
    v___x_1537_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_1529_,
        v___f_1536_,
        v_init_1531_,
        v_m_1530_,
    );
    v___f_1538_ = lean_alloc_closure(
        l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1538_, 0, v_toPure_1535_);
    v___x_1539_ = lean_apply_4(
        v_toBind_1534_,
        lean_box(0),
        lean_box(0),
        v___x_1537_,
        v___f_1538_,
    );
    return v___x_1539_;
}
pub unsafe fn l_Lean_NameMap_instForInProdNameOfMonad___aux__1(
    mut v_00_u03b1_1540_: *mut LeanObject,
    mut v_m_1541_: *mut LeanObject,
    mut v_inst_1542_: *mut LeanObject,
    mut v_00_u03b2_1543_: *mut LeanObject,
    mut v_m_1544_: *mut LeanObject,
    mut v_init_1545_: *mut LeanObject,
    mut v_f_1546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1547_ = lean_ctor_get(v_inst_1542_, 0);
    v_toBind_1548_ = lean_ctor_get(v_inst_1542_, 1);
    lean_inc(v_toBind_1548_);
    v_toPure_1549_ = lean_ctor_get(v_toApplicative_1547_, 1);
    lean_inc(v_toPure_1549_);
    v___f_1550_ = lean_alloc_closure(
        l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1550_, 0, v_f_1546_);
    v___x_1551_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_1542_,
        v___f_1550_,
        v_init_1545_,
        v_m_1544_,
    );
    v___f_1552_ = lean_alloc_closure(
        l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1552_, 0, v_toPure_1549_);
    v___x_1553_ = lean_apply_4(
        v_toBind_1548_,
        lean_box(0),
        lean_box(0),
        v___x_1551_,
        v___f_1552_,
    );
    return v___x_1553_;
}
pub unsafe fn l_Lean_NameMap_instForInProdNameOfMonad___redArg(
    mut v_inst_1554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    v___x_1555_ = lean_alloc_closure(
        l_Lean_NameMap_instForInProdNameOfMonad___aux__1 as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___x_1555_, 0, lean_box(0));
    lean_closure_set(v___x_1555_, 1, lean_box(0));
    lean_closure_set(v___x_1555_, 2, v_inst_1554_);
    return v___x_1555_;
}
pub unsafe fn l_Lean_NameMap_instForInProdNameOfMonad(
    mut v_00_u03b1_1556_: *mut LeanObject,
    mut v_m_1557_: *mut LeanObject,
    mut v_inst_1558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    v___x_1559_ = lean_alloc_closure(
        l_Lean_NameMap_instForInProdNameOfMonad___aux__1 as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___x_1559_, 0, lean_box(0));
    lean_closure_set(v___x_1559_, 1, lean_box(0));
    lean_closure_set(v___x_1559_, 2, v_inst_1558_);
    return v___x_1559_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(
    mut v_f_1560_: *mut LeanObject,
    mut v_t_1561_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1561_) == 0 {
        let mut v_k_1562_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1563_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1564_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1565_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1567_: u8 = 0;
        v_k_1562_ = lean_ctor_get(v_t_1561_, 1);
        lean_inc_n(v_k_1562_, 2);
        v_v_1563_ = lean_ctor_get(v_t_1561_, 2);
        lean_inc_n(v_v_1563_, 2);
        v_l_1564_ = lean_ctor_get(v_t_1561_, 3);
        lean_inc(v_l_1564_);
        v_r_1565_ = lean_ctor_get(v_t_1561_, 4);
        lean_inc(v_r_1565_);
        lean_dec_ref_known(v_t_1561_, 5);
        lean_inc_ref(v_f_1560_);
        v___x_1566_ = lean_apply_2(v_f_1560_, v_k_1562_, v_v_1563_);
        v___x_1567_ = (lean_unbox(v___x_1566_) as u8);
        if v___x_1567_ == 0 {
            let mut v_impl_1568_: *mut LeanObject = core::ptr::null_mut();
            let mut v_impl_1569_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_v_1563_);
            lean_dec(v_k_1562_);
            lean_inc_ref(v_f_1560_);
            v_impl_1568_ =
                l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(
                    v_f_1560_, v_l_1564_,
                );
            v_impl_1569_ =
                l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(
                    v_f_1560_, v_r_1565_,
                );
            v___x_1570_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_1568_, v_impl_1569_);
            return v___x_1570_;
        } else {
            let mut v_impl_1571_: *mut LeanObject = core::ptr::null_mut();
            let mut v_impl_1572_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_f_1560_);
            v_impl_1571_ =
                l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(
                    v_f_1560_, v_l_1564_,
                );
            v_impl_1572_ =
                l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(
                    v_f_1560_, v_r_1565_,
                );
            v___x_1573_ = l_Std_DTreeMap_Internal_Impl_link___redArg(
                v_k_1562_,
                v_v_1563_,
                v_impl_1571_,
                v_impl_1572_,
            );
            return v___x_1573_;
        }
    } else {
        lean_dec_ref(v_f_1560_);
        return v_t_1561_;
    }
}
pub unsafe fn l_Lean_NameMap_filter___redArg(
    mut v_f_1574_: *mut LeanObject,
    mut v_m_1575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    v___x_1576_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(
        v_f_1574_, v_m_1575_,
    );
    return v___x_1576_;
}
pub unsafe fn l_Lean_NameMap_filter(
    mut v_00_u03b1_1577_: *mut LeanObject,
    mut v_f_1578_: *mut LeanObject,
    mut v_m_1579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    v___x_1580_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(
        v_f_1578_, v_m_1579_,
    );
    return v___x_1580_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0(
    mut v_00_u03b1_1581_: *mut LeanObject,
    mut v_f_1582_: *mut LeanObject,
    mut v_t_1583_: *mut LeanObject,
    mut v_hl_1584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    v___x_1585_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(
        v_f_1582_, v_t_1583_,
    );
    return v___x_1585_;
}
pub unsafe fn _init_l_Lean_NameSet_empty() -> *mut LeanObject {
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    v___x_1586_ = lean_box(1);
    return v___x_1586_;
}
pub unsafe fn _init_l_Lean_NameSet_instEmptyCollection() -> *mut LeanObject {
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    v___x_1587_ = lean_box(1);
    return v___x_1587_;
}
pub unsafe fn _init_l_Lean_NameSet_instInhabited() -> *mut LeanObject {
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    v___x_1588_ = lean_box(1);
    return v___x_1588_;
}
pub unsafe fn l_Lean_NameSet_insert(
    mut v_s_1589_: *mut LeanObject,
    mut v_n_1590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1591_: u8 = 0;
    v___x_1591_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(
            v_n_1590_, v_s_1589_,
        );
    if v___x_1591_ == 0 {
        let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
        v___x_1592_ = lean_box(0);
        v___x_1593_ =
            l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
                v_n_1590_,
                v___x_1592_,
                v_s_1589_,
            );
        return v___x_1593_;
    } else {
        lean_dec(v_n_1590_);
        return v_s_1589_;
    }
}
pub unsafe fn l_Lean_NameSet_contains(
    mut v_s_1594_: *mut LeanObject,
    mut v_n_1595_: *mut LeanObject,
) -> u8 {
    let mut v___x_1596_: u8 = 0;
    v___x_1596_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(
            v_n_1595_, v_s_1594_,
        );
    return v___x_1596_;
}
pub unsafe fn l_Lean_NameSet_contains___boxed(
    mut v_s_1597_: *mut LeanObject,
    mut v_n_1598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1599_: u8 = 0;
    let mut v_r_1600_: *mut LeanObject = core::ptr::null_mut();
    v_res_1599_ = l_Lean_NameSet_contains(v_s_1597_, v_n_1598_);
    lean_dec(v_n_1598_);
    lean_dec(v_s_1597_);
    v_r_1600_ = lean_box((v_res_1599_) as usize);
    return v_r_1600_;
}
pub unsafe fn l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg___lam__0(
    mut v_f_1601_: *mut LeanObject,
    mut v_a_1602_: *mut LeanObject,
    mut v_b_1603_: *mut LeanObject,
    mut v_c_1604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    v___x_1605_ = lean_apply_2(v_f_1601_, v_a_1602_, v_c_1604_);
    return v___x_1605_;
}
pub unsafe fn l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg(
    mut v_inst_1606_: *mut LeanObject,
    mut v_m_1607_: *mut LeanObject,
    mut v_init_1608_: *mut LeanObject,
    mut v_f_1609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1610_ = lean_ctor_get(v_inst_1606_, 0);
    v_toBind_1611_ = lean_ctor_get(v_inst_1606_, 1);
    lean_inc(v_toBind_1611_);
    v_toPure_1612_ = lean_ctor_get(v_toApplicative_1610_, 1);
    lean_inc(v_toPure_1612_);
    v___f_1613_ = lean_alloc_closure(
        l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1613_, 0, v_f_1609_);
    v___x_1614_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_1606_,
        v___f_1613_,
        v_init_1608_,
        v_m_1607_,
    );
    v___f_1615_ = lean_alloc_closure(
        l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1615_, 0, v_toPure_1612_);
    v___x_1616_ = lean_apply_4(
        v_toBind_1611_,
        lean_box(0),
        lean_box(0),
        v___x_1614_,
        v___f_1615_,
    );
    return v___x_1616_;
}
pub unsafe fn l_Lean_NameSet_instForInNameOfMonad___aux__1(
    mut v_m_1617_: *mut LeanObject,
    mut v_inst_1618_: *mut LeanObject,
    mut v_00_u03b2_1619_: *mut LeanObject,
    mut v_m_1620_: *mut LeanObject,
    mut v_init_1621_: *mut LeanObject,
    mut v_f_1622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1623_ = lean_ctor_get(v_inst_1618_, 0);
    v_toBind_1624_ = lean_ctor_get(v_inst_1618_, 1);
    lean_inc(v_toBind_1624_);
    v_toPure_1625_ = lean_ctor_get(v_toApplicative_1623_, 1);
    lean_inc(v_toPure_1625_);
    v___f_1626_ = lean_alloc_closure(
        l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1626_, 0, v_f_1622_);
    v___x_1627_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_1618_,
        v___f_1626_,
        v_init_1621_,
        v_m_1620_,
    );
    v___f_1628_ = lean_alloc_closure(
        l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1628_, 0, v_toPure_1625_);
    v___x_1629_ = lean_apply_4(
        v_toBind_1624_,
        lean_box(0),
        lean_box(0),
        v___x_1627_,
        v___f_1628_,
    );
    return v___x_1629_;
}
pub unsafe fn l_Lean_NameSet_instForInNameOfMonad___redArg(
    mut v_inst_1630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    v___x_1631_ = lean_alloc_closure(
        l_Lean_NameSet_instForInNameOfMonad___aux__1 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___x_1631_, 0, lean_box(0));
    lean_closure_set(v___x_1631_, 1, v_inst_1630_);
    return v___x_1631_;
}
pub unsafe fn l_Lean_NameSet_instForInNameOfMonad(
    mut v_m_1632_: *mut LeanObject,
    mut v_inst_1633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    v___x_1634_ = lean_alloc_closure(
        l_Lean_NameSet_instForInNameOfMonad___aux__1 as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___x_1634_, 0, lean_box(0));
    lean_closure_set(v___x_1634_, 1, v_inst_1633_);
    return v___x_1634_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(
    mut v_b_u2082_1637_: *mut LeanObject,
    mut v_x_1638_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1638_) == 0 {
        let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
        v___x_1639_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1639_, 0, v_b_u2082_1637_);
        return v___x_1639_;
    } else {
        let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
        v___x_1640_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___closed__0;
        return v___x_1640_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___boxed(
    mut v_b_u2082_1641_: *mut LeanObject,
    mut v_x_1642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1643_: *mut LeanObject = core::ptr::null_mut();
    v_res_1643_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(v_b_u2082_1641_, v_x_1642_);
    lean_dec(v_x_1642_);
    return v_res_1643_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(
    mut v_b_u2082_1644_: *mut LeanObject,
    mut v_k_1645_: *mut LeanObject,
    mut v_t_1646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1654_: u8 = 0;
    let mut v___x_1655_: u8 = 0;
    let mut v_impl_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1666_: u8 = 0;
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1646_) == 0 {
                    v_size_1647_ = lean_ctor_get(v_t_1646_, 0);
                    v_k_1648_ = lean_ctor_get(v_t_1646_, 1);
                    v_v_1649_ = lean_ctor_get(v_t_1646_, 2);
                    v_l_1650_ = lean_ctor_get(v_t_1646_, 3);
                    v_r_1651_ = lean_ctor_get(v_t_1646_, 4);
                    v_isSharedCheck_1666_ = (!lean_is_exclusive(v_t_1646_)) as u8;
                    if v_isSharedCheck_1666_ == 0 {
                        v___x_1653_ = v_t_1646_;
                        v_isShared_1654_ = v_isSharedCheck_1666_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_1651_);
                        lean_inc(v_l_1650_);
                        lean_inc(v_v_1649_);
                        lean_inc(v_k_1648_);
                        lean_inc(v_size_1647_);
                        lean_dec(v_t_1646_);
                        v___x_1653_ = lean_box(0);
                        v_isShared_1654_ = v_isSharedCheck_1666_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1667_ = lean_box(0);
                    v___x_1668_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(v_b_u2082_1644_, v___x_1667_);
                    v_val_1669_ = lean_ctor_get(v___x_1668_, 0);
                    lean_inc(v_val_1669_);
                    lean_dec(v___x_1668_);
                    v___x_1670_ = lean_unsigned_to_nat(1);
                    v___x_1671_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_1671_, 0, v___x_1670_);
                    lean_ctor_set(v___x_1671_, 1, v_k_1645_);
                    lean_ctor_set(v___x_1671_, 2, v_val_1669_);
                    lean_ctor_set(v___x_1671_, 3, v_t_1646_);
                    lean_ctor_set(v___x_1671_, 4, v_t_1646_);
                    return v___x_1671_;
                }
            }
            1 => {
                v___x_1655_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1645_, v_k_1648_);
                match v___x_1655_ {
                    0 => {
                        lean_del_object(v___x_1653_);
                        lean_dec(v_size_1647_);
                        v_impl_1656_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_b_u2082_1644_, v_k_1645_, v_l_1650_);
                        v___x_1657_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(
                            v_k_1648_,
                            v_v_1649_,
                            v_impl_1656_,
                            v_r_1651_,
                        );
                        return v___x_1657_;
                    }
                    1 => {
                        lean_dec(v_k_1648_);
                        v___x_1658_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1658_, 0, v_v_1649_);
                        v___x_1659_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(v_b_u2082_1644_, v___x_1658_);
                        lean_dec_ref_known(v___x_1658_, 1);
                        v_val_1660_ = lean_ctor_get(v___x_1659_, 0);
                        lean_inc(v_val_1660_);
                        lean_dec(v___x_1659_);
                        if v_isShared_1654_ == 0 {
                            lean_ctor_set(v___x_1653_, 2, v_val_1660_);
                            lean_ctor_set(v___x_1653_, 1, v_k_1645_);
                            v___x_1662_ = v___x_1653_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_size_1647_);
                            lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_k_1645_);
                            lean_ctor_set(v_reuseFailAlloc_1663_, 2, v_val_1660_);
                            lean_ctor_set(v_reuseFailAlloc_1663_, 3, v_l_1650_);
                            lean_ctor_set(v_reuseFailAlloc_1663_, 4, v_r_1651_);
                            v___x_1662_ = v_reuseFailAlloc_1663_;
                            state = 2;
                            continue;
                        }
                    }
                    _ => {
                        lean_del_object(v___x_1653_);
                        lean_dec(v_size_1647_);
                        v_impl_1664_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_b_u2082_1644_, v_k_1645_, v_r_1651_);
                        v___x_1665_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(
                            v_k_1648_,
                            v_v_1649_,
                            v_l_1650_,
                            v_impl_1664_,
                        );
                        return v___x_1665_;
                    }
                }
            }
            2 => {
                return v___x_1662_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(
    mut v_init_1672_: *mut LeanObject,
    mut v_x_1673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1673_) == 0 {
                    v_k_1674_ = lean_ctor_get(v_x_1673_, 1);
                    lean_inc(v_k_1674_);
                    v_v_1675_ = lean_ctor_get(v_x_1673_, 2);
                    lean_inc(v_v_1675_);
                    v_l_1676_ = lean_ctor_get(v_x_1673_, 3);
                    lean_inc(v_l_1676_);
                    v_r_1677_ = lean_ctor_get(v_x_1673_, 4);
                    lean_inc(v_r_1677_);
                    lean_dec_ref_known(v_x_1673_, 5);
                    v___x_1678_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(v_init_1672_, v_l_1676_);
                    v___x_1679_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_v_1675_, v_k_1674_, v___x_1678_);
                    v_init_1672_ = v___x_1679_;
                    v_x_1673_ = v_r_1677_;
                    state = 0;
                    continue;
                } else {
                    return v_init_1672_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_NameSet_append(
    mut v_s_1681_: *mut LeanObject,
    mut v_t_1682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    v___x_1683_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(v_s_1681_, v_t_1682_);
    return v___x_1683_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0(
    mut v_b_u2082_1684_: *mut LeanObject,
    mut v_k_1685_: *mut LeanObject,
    mut v_t_1686_: *mut LeanObject,
    mut v_hl_1687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    v___x_1688_ =
        l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(
            v_b_u2082_1684_,
            v_k_1685_,
            v_t_1686_,
        );
    return v___x_1688_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1(
    mut v_init_1689_: *mut LeanObject,
    mut v_t_1690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    v___x_1691_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(v_init_1689_, v_t_1690_);
    return v___x_1691_;
}
pub unsafe fn l_Lean_NameSet_instSingletonName___lam__0(
    mut v_n_1694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    v___x_1695_ = lean_box(1);
    v___x_1696_ = l_Lean_NameSet_insert(v___x_1695_, v_n_1694_);
    return v___x_1696_;
}
pub unsafe fn l_Lean_NameSet_instInter___lam__0(
    mut v_t_1700_: *mut LeanObject,
    mut v_c_1701_: *mut LeanObject,
    mut v_a_1702_: *mut LeanObject,
    mut v_x_1703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1704_: u8 = 0;
    v___x_1704_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(
            v_a_1702_, v_t_1700_,
        );
    if v___x_1704_ == 0 {
        lean_dec(v_a_1702_);
        return v_c_1701_;
    } else {
        let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
        v___x_1705_ = l_Lean_NameSet_insert(v_c_1701_, v_a_1702_);
        return v___x_1705_;
    }
}
pub unsafe fn l_Lean_NameSet_instInter___lam__0___boxed(
    mut v_t_1706_: *mut LeanObject,
    mut v_c_1707_: *mut LeanObject,
    mut v_a_1708_: *mut LeanObject,
    mut v_x_1709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1710_: *mut LeanObject = core::ptr::null_mut();
    v_res_1710_ = l_Lean_NameSet_instInter___lam__0(v_t_1706_, v_c_1707_, v_a_1708_, v_x_1709_);
    lean_dec(v_t_1706_);
    return v_res_1710_;
}
pub unsafe fn l_Lean_NameSet_instInter___lam__1(
    mut v_s_1711_: *mut LeanObject,
    mut v_t_1712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    v___f_1713_ = lean_alloc_closure(
        l_Lean_NameSet_instInter___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1713_, 0, v_t_1712_);
    v___x_1714_ = lean_box(1);
    v___x_1715_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1713_, v___x_1714_, v_s_1711_);
    return v___x_1715_;
}
pub unsafe fn l_Lean_NameSet_instSDiff___lam__0(
    mut v___x_1718_: *mut LeanObject,
    mut v_c_1719_: *mut LeanObject,
    mut v_a_1720_: *mut LeanObject,
    mut v_x_1721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    v___x_1722_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_1718_, v_a_1720_, v_c_1719_);
    return v___x_1722_;
}
pub unsafe fn l_Lean_NameSet_instSDiff___lam__1(
    mut v_s_1726_: *mut LeanObject,
    mut v_t_1727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    v___f_1728_ = l_Lean_NameSet_instSDiff___lam__1___closed__1;
    v___x_1729_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1728_, v_s_1726_, v_t_1727_);
    return v___x_1729_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(
    mut v_f_1732_: *mut LeanObject,
    mut v_t_1733_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1733_) == 0 {
        let mut v_k_1734_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_1735_: *mut LeanObject = core::ptr::null_mut();
        let mut v_l_1736_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_1737_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1739_: u8 = 0;
        v_k_1734_ = lean_ctor_get(v_t_1733_, 1);
        lean_inc_n(v_k_1734_, 2);
        v_v_1735_ = lean_ctor_get(v_t_1733_, 2);
        lean_inc(v_v_1735_);
        v_l_1736_ = lean_ctor_get(v_t_1733_, 3);
        lean_inc(v_l_1736_);
        v_r_1737_ = lean_ctor_get(v_t_1733_, 4);
        lean_inc(v_r_1737_);
        lean_dec_ref_known(v_t_1733_, 5);
        lean_inc_ref(v_f_1732_);
        v___x_1738_ = lean_apply_1(v_f_1732_, v_k_1734_);
        v___x_1739_ = (lean_unbox(v___x_1738_) as u8);
        if v___x_1739_ == 0 {
            let mut v_impl_1740_: *mut LeanObject = core::ptr::null_mut();
            let mut v_impl_1741_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_v_1735_);
            lean_dec(v_k_1734_);
            lean_inc_ref(v_f_1732_);
            v_impl_1740_ =
                l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(
                    v_f_1732_, v_l_1736_,
                );
            v_impl_1741_ =
                l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(
                    v_f_1732_, v_r_1737_,
                );
            v___x_1742_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_1740_, v_impl_1741_);
            return v___x_1742_;
        } else {
            let mut v_impl_1743_: *mut LeanObject = core::ptr::null_mut();
            let mut v_impl_1744_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_f_1732_);
            v_impl_1743_ =
                l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(
                    v_f_1732_, v_l_1736_,
                );
            v_impl_1744_ =
                l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(
                    v_f_1732_, v_r_1737_,
                );
            v___x_1745_ = l_Std_DTreeMap_Internal_Impl_link___redArg(
                v_k_1734_,
                v_v_1735_,
                v_impl_1743_,
                v_impl_1744_,
            );
            return v___x_1745_;
        }
    } else {
        lean_dec_ref(v_f_1732_);
        return v_t_1733_;
    }
}
pub unsafe fn l_Lean_NameSet_filter(
    mut v_f_1746_: *mut LeanObject,
    mut v_s_1747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    v___x_1748_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(
        v_f_1746_, v_s_1747_,
    );
    return v___x_1748_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0(
    mut v_f_1749_: *mut LeanObject,
    mut v_t_1750_: *mut LeanObject,
    mut v_hl_1751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    v___x_1752_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(
        v_f_1749_, v_t_1750_,
    );
    return v___x_1752_;
}
pub unsafe fn l_Lean_NameSet_ofList(mut v_l_1753_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    v___x_1754_ = l_Lean_NameSet_instSDiff___lam__1___closed__0;
    v___x_1755_ = l_Std_TreeSet_ofList___redArg(v_l_1753_, v___x_1754_);
    return v___x_1755_;
}
pub unsafe fn l_Lean_NameSet_ofList___boxed(mut v_l_1756_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1757_: *mut LeanObject = core::ptr::null_mut();
    v_res_1757_ = l_Lean_NameSet_ofList(v_l_1756_);
    lean_dec(v_l_1756_);
    return v_res_1757_;
}
pub unsafe fn l_Lean_NameSet_ofArray(mut v_l_1758_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    v___x_1759_ = l_Lean_NameSet_instSDiff___lam__1___closed__0;
    v___x_1760_ = l_Std_TreeSet_ofArray___redArg(v_l_1758_, v___x_1759_);
    return v___x_1760_;
}
pub unsafe fn l_Lean_NameSet_ofArray___boxed(mut v_l_1761_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1762_: *mut LeanObject = core::ptr::null_mut();
    v_res_1762_ = l_Lean_NameSet_ofArray(v_l_1761_);
    lean_dec_ref(v_l_1761_);
    return v_res_1762_;
}
pub unsafe fn _init_l_Lean_NameSSet_empty___closed__2() -> *mut LeanObject {
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    v___x_1765_ = l_Lean_NameSSet_empty___closed__1;
    v___x_1766_ = l_Lean_NameSSet_empty___closed__0;
    v___x_1767_ = l_Lean_SMap_empty(lean_box(0), lean_box(0), v___x_1766_, v___x_1765_);
    return v___x_1767_;
}
pub unsafe fn _init_l_Lean_NameSSet_empty() -> *mut LeanObject {
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    v___x_1768_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_NameSSet_empty___closed__2),
        core::ptr::addr_of_mut!(l_Lean_NameSSet_empty___closed__2_once),
        _init_l_Lean_NameSSet_empty___closed__2,
    );
    return v___x_1768_;
}
pub unsafe fn _init_l_Lean_NameSSet_instEmptyCollection() -> *mut LeanObject {
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    v___x_1769_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_NameSSet_empty___closed__2),
        core::ptr::addr_of_mut!(l_Lean_NameSSet_empty___closed__2_once),
        _init_l_Lean_NameSSet_empty___closed__2,
    );
    return v___x_1769_;
}
pub unsafe fn _init_l_Lean_NameSSet_instInhabited() -> *mut LeanObject {
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    v___x_1770_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_NameSSet_empty___closed__2),
        core::ptr::addr_of_mut!(l_Lean_NameSSet_empty___closed__2_once),
        _init_l_Lean_NameSSet_empty___closed__2,
    );
    return v___x_1770_;
}
pub unsafe fn l_Lean_NameSSet_insert(
    mut v_s_1771_: *mut LeanObject,
    mut v_n_1772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    v___x_1773_ = l_Lean_NameSSet_empty___closed__0;
    v___x_1774_ = l_Lean_NameSSet_empty___closed__1;
    v___x_1775_ = lean_box(0);
    v___x_1776_ =
        l_Lean_SMap_insert___redArg(v___x_1773_, v___x_1774_, v_s_1771_, v_n_1772_, v___x_1775_);
    return v___x_1776_;
}
pub unsafe fn l_Lean_NameSSet_contains(
    mut v_s_1777_: *mut LeanObject,
    mut v_n_1778_: *mut LeanObject,
) -> u8 {
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: u8 = 0;
    v___x_1779_ = l_Lean_NameSSet_empty___closed__0;
    v___x_1780_ = l_Lean_NameSSet_empty___closed__1;
    v___x_1781_ = l_Lean_SMap_contains___redArg(v___x_1779_, v___x_1780_, v_s_1777_, v_n_1778_);
    return v___x_1781_;
}
pub unsafe fn l_Lean_NameSSet_contains___boxed(
    mut v_s_1782_: *mut LeanObject,
    mut v_n_1783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1784_: u8 = 0;
    let mut v_r_1785_: *mut LeanObject = core::ptr::null_mut();
    v_res_1784_ = l_Lean_NameSSet_contains(v_s_1782_, v_n_1783_);
    v_r_1785_ = lean_box((v_res_1784_) as usize);
    return v_r_1785_;
}
pub unsafe fn _init_l_Lean_NameHashSet_empty___closed__0() -> *mut LeanObject {
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    v___x_1786_ = lean_box(0);
    v___x_1787_ = lean_unsigned_to_nat(16);
    v___x_1788_ = lean_mk_array(v___x_1787_, v___x_1786_);
    return v___x_1788_;
}
pub unsafe fn _init_l_Lean_NameHashSet_empty___closed__1() -> *mut LeanObject {
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    v___x_1789_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_NameHashSet_empty___closed__0),
        core::ptr::addr_of_mut!(l_Lean_NameHashSet_empty___closed__0_once),
        _init_l_Lean_NameHashSet_empty___closed__0,
    );
    v___x_1790_ = lean_unsigned_to_nat(0);
    v___x_1791_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1791_, 0, v___x_1790_);
    lean_ctor_set(v___x_1791_, 1, v___x_1789_);
    return v___x_1791_;
}
pub unsafe fn _init_l_Lean_NameHashSet_empty() -> *mut LeanObject {
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    v___x_1792_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_NameHashSet_empty___closed__1),
        core::ptr::addr_of_mut!(l_Lean_NameHashSet_empty___closed__1_once),
        _init_l_Lean_NameHashSet_empty___closed__1,
    );
    return v___x_1792_;
}
pub unsafe fn _init_l_Lean_NameHashSet_instEmptyCollection() -> *mut LeanObject {
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    v___x_1793_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_NameHashSet_empty___closed__1),
        core::ptr::addr_of_mut!(l_Lean_NameHashSet_empty___closed__1_once),
        _init_l_Lean_NameHashSet_empty___closed__1,
    );
    return v___x_1793_;
}
pub unsafe fn _init_l_Lean_NameHashSet_instInhabited() -> *mut LeanObject {
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    v___x_1794_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_NameHashSet_empty___closed__1),
        core::ptr::addr_of_mut!(l_Lean_NameHashSet_empty___closed__1_once),
        _init_l_Lean_NameHashSet_empty___closed__1,
    );
    return v___x_1794_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(
    mut v_a_1795_: *mut LeanObject,
    mut v_x_1796_: *mut LeanObject,
) -> u8 {
    let mut v___x_1797_: u8 = 0;
    let mut v_key_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1796_) == 0 {
                    v___x_1797_ = 0;
                    return v___x_1797_;
                } else {
                    v_key_1798_ = lean_ctor_get(v_x_1796_, 0);
                    v_tail_1799_ = lean_ctor_get(v_x_1796_, 2);
                    v___x_1800_ = lean_name_eq(v_key_1798_, v_a_1795_);
                    if v___x_1800_ == 0 {
                        v_x_1796_ = v_tail_1799_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1800_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg___boxed(
    mut v_a_1802_: *mut LeanObject,
    mut v_x_1803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1804_: u8 = 0;
    let mut v_r_1805_: *mut LeanObject = core::ptr::null_mut();
    v_res_1804_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_1802_, v_x_1803_);
    lean_dec(v_x_1803_);
    lean_dec(v_a_1802_);
    v_r_1805_ = lean_box((v_res_1804_) as usize);
    return v_r_1805_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0()
-> u64 {
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: u64 = 0;
    v___x_1806_ = lean_unsigned_to_nat(1723);
    v___x_1807_ = lean_uint64_of_nat(v___x_1806_);
    return v___x_1807_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_1808_: *mut LeanObject,
    mut v_x_1809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1815_: u8 = 0;
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1818_: u64 = 0;
    let mut v___x_1819_: u64 = 0;
    let mut v___x_1820_: u64 = 0;
    let mut v_fold_1821_: u64 = 0;
    let mut v___x_1822_: u64 = 0;
    let mut v___x_1823_: u64 = 0;
    let mut v___x_1824_: u64 = 0;
    let mut v___x_1825_: usize = 0;
    let mut v___x_1826_: usize = 0;
    let mut v___x_1827_: usize = 0;
    let mut v___x_1828_: usize = 0;
    let mut v___x_1829_: usize = 0;
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: u64 = 0;
    let mut v_hash_1837_: u64 = 0;
    let mut v_isSharedCheck_1838_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1809_) == 0 {
                    return v_x_1808_;
                } else {
                    v_key_1810_ = lean_ctor_get(v_x_1809_, 0);
                    v_value_1811_ = lean_ctor_get(v_x_1809_, 1);
                    v_tail_1812_ = lean_ctor_get(v_x_1809_, 2);
                    v_isSharedCheck_1838_ = (!lean_is_exclusive(v_x_1809_)) as u8;
                    if v_isSharedCheck_1838_ == 0 {
                        v___x_1814_ = v_x_1809_;
                        v_isShared_1815_ = v_isSharedCheck_1838_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1812_);
                        lean_inc(v_value_1811_);
                        lean_inc(v_key_1810_);
                        lean_dec(v_x_1809_);
                        v___x_1814_ = lean_box(0);
                        v_isShared_1815_ = v_isSharedCheck_1838_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1816_ = lean_array_get_size(v_x_1808_);
                if lean_obj_tag(v_key_1810_) == 0 {
                    v___x_1836_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_1818_ = v___x_1836_;
                    state = 2;
                    continue;
                } else {
                    v_hash_1837_ = lean_ctor_get_uint64(
                        v_key_1810_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1818_ = v_hash_1837_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1819_ = 32u64;
                v___x_1820_ = lean_uint64_shift_right(v___y_1818_, v___x_1819_);
                v_fold_1821_ = lean_uint64_xor(v___y_1818_, v___x_1820_);
                v___x_1822_ = 16u64;
                v___x_1823_ = lean_uint64_shift_right(v_fold_1821_, v___x_1822_);
                v___x_1824_ = lean_uint64_xor(v_fold_1821_, v___x_1823_);
                v___x_1825_ = lean_uint64_to_usize(v___x_1824_);
                v___x_1826_ = lean_usize_of_nat(v___x_1816_);
                v___x_1827_ = 1usize;
                v___x_1828_ = lean_usize_sub(v___x_1826_, v___x_1827_);
                v___x_1829_ = lean_usize_land(v___x_1825_, v___x_1828_);
                v___x_1830_ = lean_array_uget_borrowed(v_x_1808_, v___x_1829_);
                lean_inc(v___x_1830_);
                if v_isShared_1815_ == 0 {
                    lean_ctor_set(v___x_1814_, 2, v___x_1830_);
                    v___x_1832_ = v___x_1814_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_key_1810_);
                    lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_value_1811_);
                    lean_ctor_set(v_reuseFailAlloc_1835_, 2, v___x_1830_);
                    v___x_1832_ = v_reuseFailAlloc_1835_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1833_ = lean_array_uset(v_x_1808_, v___x_1829_, v___x_1832_);
                v_x_1808_ = v___x_1833_;
                v_x_1809_ = v_tail_1812_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2___redArg(
    mut v_i_1839_: *mut LeanObject,
    mut v_source_1840_: *mut LeanObject,
    mut v_target_1841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: u8 = 0;
    let mut v_es_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1842_ = lean_array_get_size(v_source_1840_);
                v___x_1843_ = lean_nat_dec_lt(v_i_1839_, v___x_1842_);
                if v___x_1843_ == 0 {
                    lean_dec_ref(v_source_1840_);
                    lean_dec(v_i_1839_);
                    return v_target_1841_;
                } else {
                    v_es_1844_ = lean_array_fget(v_source_1840_, v_i_1839_);
                    v___x_1845_ = lean_box(0);
                    v_source_1846_ = lean_array_fset(v_source_1840_, v_i_1839_, v___x_1845_);
                    v_target_1847_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1841_, v_es_1844_);
                    v___x_1848_ = lean_unsigned_to_nat(1);
                    v___x_1849_ = lean_nat_add(v_i_1839_, v___x_1848_);
                    lean_dec(v_i_1839_);
                    v_i_1839_ = v___x_1849_;
                    v_source_1840_ = v_source_1846_;
                    v_target_1841_ = v_target_1847_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1___redArg(
    mut v_data_1851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    v___x_1852_ = lean_array_get_size(v_data_1851_);
    v___x_1853_ = lean_unsigned_to_nat(2);
    v_nbuckets_1854_ = lean_nat_mul(v___x_1852_, v___x_1853_);
    v___x_1855_ = lean_unsigned_to_nat(0);
    v___x_1856_ = lean_box(0);
    v___x_1857_ = lean_mk_array(v_nbuckets_1854_, v___x_1856_);
    v___x_1858_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2___redArg(v___x_1855_, v_data_1851_, v___x_1857_);
    return v___x_1858_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0___redArg(
    mut v_m_1859_: *mut LeanObject,
    mut v_a_1860_: *mut LeanObject,
    mut v_b_1861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1866_: u64 = 0;
    let mut v___x_1867_: u64 = 0;
    let mut v___x_1868_: u64 = 0;
    let mut v_fold_1869_: u64 = 0;
    let mut v___x_1870_: u64 = 0;
    let mut v___x_1871_: u64 = 0;
    let mut v___x_1872_: u64 = 0;
    let mut v___x_1873_: usize = 0;
    let mut v___x_1874_: usize = 0;
    let mut v___x_1875_: usize = 0;
    let mut v___x_1876_: usize = 0;
    let mut v___x_1877_: usize = 0;
    let mut v_bkt_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: u8 = 0;
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1882_: u8 = 0;
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: u8 = 0;
    let mut v_val_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1900_: u8 = 0;
    let mut v_unused_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: u64 = 0;
    let mut v_hash_1904_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1862_ = lean_ctor_get(v_m_1859_, 0);
                v_buckets_1863_ = lean_ctor_get(v_m_1859_, 1);
                v___x_1864_ = lean_array_get_size(v_buckets_1863_);
                if lean_obj_tag(v_a_1860_) == 0 {
                    v___x_1903_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_1866_ = v___x_1903_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1904_ = lean_ctor_get_uint64(
                        v_a_1860_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1866_ = v_hash_1904_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1867_ = 32u64;
                v___x_1868_ = lean_uint64_shift_right(v___y_1866_, v___x_1867_);
                v_fold_1869_ = lean_uint64_xor(v___y_1866_, v___x_1868_);
                v___x_1870_ = 16u64;
                v___x_1871_ = lean_uint64_shift_right(v_fold_1869_, v___x_1870_);
                v___x_1872_ = lean_uint64_xor(v_fold_1869_, v___x_1871_);
                v___x_1873_ = lean_uint64_to_usize(v___x_1872_);
                v___x_1874_ = lean_usize_of_nat(v___x_1864_);
                v___x_1875_ = 1usize;
                v___x_1876_ = lean_usize_sub(v___x_1874_, v___x_1875_);
                v___x_1877_ = lean_usize_land(v___x_1873_, v___x_1876_);
                v_bkt_1878_ = lean_array_uget_borrowed(v_buckets_1863_, v___x_1877_);
                v___x_1879_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_1860_, v_bkt_1878_);
                if v___x_1879_ == 0 {
                    lean_inc_ref(v_buckets_1863_);
                    lean_inc(v_size_1862_);
                    v_isSharedCheck_1900_ = (!lean_is_exclusive(v_m_1859_)) as u8;
                    if v_isSharedCheck_1900_ == 0 {
                        v_unused_1901_ = lean_ctor_get(v_m_1859_, 1);
                        lean_dec(v_unused_1901_);
                        v_unused_1902_ = lean_ctor_get(v_m_1859_, 0);
                        lean_dec(v_unused_1902_);
                        v___x_1881_ = v_m_1859_;
                        v_isShared_1882_ = v_isSharedCheck_1900_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_1859_);
                        v___x_1881_ = lean_box(0);
                        v_isShared_1882_ = v_isSharedCheck_1900_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_b_1861_);
                    lean_dec(v_a_1860_);
                    return v_m_1859_;
                }
            }
            2 => {
                v___x_1883_ = lean_unsigned_to_nat(1);
                v_size_x27_1884_ = lean_nat_add(v_size_1862_, v___x_1883_);
                lean_dec(v_size_1862_);
                lean_inc(v_bkt_1878_);
                v___x_1885_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1885_, 0, v_a_1860_);
                lean_ctor_set(v___x_1885_, 1, v_b_1861_);
                lean_ctor_set(v___x_1885_, 2, v_bkt_1878_);
                v_buckets_x27_1886_ = lean_array_uset(v_buckets_1863_, v___x_1877_, v___x_1885_);
                v___x_1887_ = lean_unsigned_to_nat(4);
                v___x_1888_ = lean_nat_mul(v_size_x27_1884_, v___x_1887_);
                v___x_1889_ = lean_unsigned_to_nat(3);
                v___x_1890_ = lean_nat_div(v___x_1888_, v___x_1889_);
                lean_dec(v___x_1888_);
                v___x_1891_ = lean_array_get_size(v_buckets_x27_1886_);
                v___x_1892_ = lean_nat_dec_le(v___x_1890_, v___x_1891_);
                lean_dec(v___x_1890_);
                if v___x_1892_ == 0 {
                    v_val_1893_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1___redArg(v_buckets_x27_1886_);
                    if v_isShared_1882_ == 0 {
                        lean_ctor_set(v___x_1881_, 1, v_val_1893_);
                        lean_ctor_set(v___x_1881_, 0, v_size_x27_1884_);
                        v___x_1895_ = v___x_1881_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_size_x27_1884_);
                        lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_val_1893_);
                        v___x_1895_ = v_reuseFailAlloc_1896_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_1882_ == 0 {
                        lean_ctor_set(v___x_1881_, 1, v_buckets_x27_1886_);
                        lean_ctor_set(v___x_1881_, 0, v_size_x27_1884_);
                        v___x_1898_ = v___x_1881_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_size_x27_1884_);
                        lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_buckets_x27_1886_);
                        v___x_1898_ = v_reuseFailAlloc_1899_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1895_;
            }
            4 => {
                return v___x_1898_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_NameHashSet_insert(
    mut v_s_1905_: *mut LeanObject,
    mut v_n_1906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    v___x_1907_ = lean_box(0);
    v___x_1908_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0___redArg(v_s_1905_, v_n_1906_, v___x_1907_);
    return v___x_1908_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0(
    mut v_00_u03b2_1909_: *mut LeanObject,
    mut v_m_1910_: *mut LeanObject,
    mut v_a_1911_: *mut LeanObject,
    mut v_b_1912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    v___x_1913_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0___redArg(v_m_1910_, v_a_1911_, v_b_1912_);
    return v___x_1913_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0(
    mut v_00_u03b2_1914_: *mut LeanObject,
    mut v_a_1915_: *mut LeanObject,
    mut v_x_1916_: *mut LeanObject,
) -> u8 {
    let mut v___x_1917_: u8 = 0;
    v___x_1917_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_1915_, v_x_1916_);
    return v___x_1917_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___boxed(
    mut v_00_u03b2_1918_: *mut LeanObject,
    mut v_a_1919_: *mut LeanObject,
    mut v_x_1920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1921_: u8 = 0;
    let mut v_r_1922_: *mut LeanObject = core::ptr::null_mut();
    v_res_1921_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0(v_00_u03b2_1918_, v_a_1919_, v_x_1920_);
    lean_dec(v_x_1920_);
    lean_dec(v_a_1919_);
    v_r_1922_ = lean_box((v_res_1921_) as usize);
    return v_r_1922_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1(
    mut v_00_u03b2_1923_: *mut LeanObject,
    mut v_data_1924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    v___x_1925_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1___redArg(v_data_1924_);
    return v___x_1925_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1926_: *mut LeanObject,
    mut v_i_1927_: *mut LeanObject,
    mut v_source_1928_: *mut LeanObject,
    mut v_target_1929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    v___x_1930_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2___redArg(v_i_1927_, v_source_1928_, v_target_1929_);
    return v___x_1930_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_1931_: *mut LeanObject,
    mut v_x_1932_: *mut LeanObject,
    mut v_x_1933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    v___x_1934_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1932_, v_x_1933_);
    return v___x_1934_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(
    mut v_m_1935_: *mut LeanObject,
    mut v_a_1936_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1940_: u64 = 0;
    let mut v___x_1941_: u64 = 0;
    let mut v___x_1942_: u64 = 0;
    let mut v_fold_1943_: u64 = 0;
    let mut v___x_1944_: u64 = 0;
    let mut v___x_1945_: u64 = 0;
    let mut v___x_1946_: u64 = 0;
    let mut v___x_1947_: usize = 0;
    let mut v___x_1948_: usize = 0;
    let mut v___x_1949_: usize = 0;
    let mut v___x_1950_: usize = 0;
    let mut v___x_1951_: usize = 0;
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: u8 = 0;
    let mut v___x_1954_: u64 = 0;
    let mut v_hash_1955_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_1937_ = lean_ctor_get(v_m_1935_, 1);
                v___x_1938_ = lean_array_get_size(v_buckets_1937_);
                if lean_obj_tag(v_a_1936_) == 0 {
                    v___x_1954_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_1940_ = v___x_1954_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1955_ = lean_ctor_get_uint64(
                        v_a_1936_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1940_ = v_hash_1955_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1941_ = 32u64;
                v___x_1942_ = lean_uint64_shift_right(v___y_1940_, v___x_1941_);
                v_fold_1943_ = lean_uint64_xor(v___y_1940_, v___x_1942_);
                v___x_1944_ = 16u64;
                v___x_1945_ = lean_uint64_shift_right(v_fold_1943_, v___x_1944_);
                v___x_1946_ = lean_uint64_xor(v_fold_1943_, v___x_1945_);
                v___x_1947_ = lean_uint64_to_usize(v___x_1946_);
                v___x_1948_ = lean_usize_of_nat(v___x_1938_);
                v___x_1949_ = 1usize;
                v___x_1950_ = lean_usize_sub(v___x_1948_, v___x_1949_);
                v___x_1951_ = lean_usize_land(v___x_1947_, v___x_1950_);
                v___x_1952_ = lean_array_uget_borrowed(v_buckets_1937_, v___x_1951_);
                v___x_1953_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_1936_, v___x_1952_);
                return v___x_1953_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg___boxed(
    mut v_m_1956_: *mut LeanObject,
    mut v_a_1957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1958_: u8 = 0;
    let mut v_r_1959_: *mut LeanObject = core::ptr::null_mut();
    v_res_1958_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_m_1956_, v_a_1957_);
    lean_dec(v_a_1957_);
    lean_dec_ref(v_m_1956_);
    v_r_1959_ = lean_box((v_res_1958_) as usize);
    return v_r_1959_;
}
pub unsafe fn l_Lean_NameHashSet_contains(
    mut v_s_1960_: *mut LeanObject,
    mut v_n_1961_: *mut LeanObject,
) -> u8 {
    let mut v___x_1962_: u8 = 0;
    v___x_1962_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_s_1960_, v_n_1961_);
    return v___x_1962_;
}
pub unsafe fn l_Lean_NameHashSet_contains___boxed(
    mut v_s_1963_: *mut LeanObject,
    mut v_n_1964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1965_: u8 = 0;
    let mut v_r_1966_: *mut LeanObject = core::ptr::null_mut();
    v_res_1965_ = l_Lean_NameHashSet_contains(v_s_1963_, v_n_1964_);
    lean_dec(v_n_1964_);
    lean_dec_ref(v_s_1963_);
    v_r_1966_ = lean_box((v_res_1965_) as usize);
    return v_r_1966_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0(
    mut v_00_u03b2_1967_: *mut LeanObject,
    mut v_m_1968_: *mut LeanObject,
    mut v_a_1969_: *mut LeanObject,
) -> u8 {
    let mut v___x_1970_: u8 = 0;
    v___x_1970_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_m_1968_, v_a_1969_);
    return v___x_1970_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___boxed(
    mut v_00_u03b2_1971_: *mut LeanObject,
    mut v_m_1972_: *mut LeanObject,
    mut v_a_1973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1974_: u8 = 0;
    let mut v_r_1975_: *mut LeanObject = core::ptr::null_mut();
    v_res_1974_ =
        l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0(
            v_00_u03b2_1971_,
            v_m_1972_,
            v_a_1973_,
        );
    lean_dec(v_a_1973_);
    lean_dec_ref(v_m_1972_);
    v_r_1975_ = lean_box((v_res_1974_) as usize);
    return v_r_1975_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0(
    mut v_f_1976_: *mut LeanObject,
    mut v_acc_1977_: *mut LeanObject,
    mut v_a_1978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1984_: u8 = 0;
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: u8 = 0;
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1992_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1978_) == 0 {
                    lean_dec_ref(v_f_1976_);
                    return v_acc_1977_;
                } else {
                    v_key_1979_ = lean_ctor_get(v_a_1978_, 0);
                    v_value_1980_ = lean_ctor_get(v_a_1978_, 1);
                    v_tail_1981_ = lean_ctor_get(v_a_1978_, 2);
                    v_isSharedCheck_1992_ = (!lean_is_exclusive(v_a_1978_)) as u8;
                    if v_isSharedCheck_1992_ == 0 {
                        v___x_1983_ = v_a_1978_;
                        v_isShared_1984_ = v_isSharedCheck_1992_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1981_);
                        lean_inc(v_value_1980_);
                        lean_inc(v_key_1979_);
                        lean_dec(v_a_1978_);
                        v___x_1983_ = lean_box(0);
                        v_isShared_1984_ = v_isSharedCheck_1992_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_f_1976_);
                lean_inc(v_key_1979_);
                v___x_1985_ = lean_apply_1(v_f_1976_, v_key_1979_);
                v___x_1986_ = (lean_unbox(v___x_1985_) as u8);
                if v___x_1986_ == 0 {
                    lean_del_object(v___x_1983_);
                    lean_dec(v_value_1980_);
                    lean_dec(v_key_1979_);
                    v_a_1978_ = v_tail_1981_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_1984_ == 0 {
                        lean_ctor_set(v___x_1983_, 2, v_acc_1977_);
                        v___x_1989_ = v___x_1983_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_key_1979_);
                        lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_value_1980_);
                        lean_ctor_set(v_reuseFailAlloc_1991_, 2, v_acc_1977_);
                        v___x_1989_ = v_reuseFailAlloc_1991_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_acc_1977_ = v___x_1989_;
                v_a_1978_ = v_tail_1981_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(
    mut v_f_1993_: *mut LeanObject,
    mut v_sz_1994_: usize,
    mut v_i_1995_: usize,
    mut v_bs_1996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1997_: u8 = 0;
    let mut v_v_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: usize = 0;
    let mut v___x_2004_: usize = 0;
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1997_ = lean_usize_dec_lt(v_i_1995_, v_sz_1994_);
                if v___x_1997_ == 0 {
                    lean_dec_ref(v_f_1993_);
                    return v_bs_1996_;
                } else {
                    v_v_1998_ = lean_array_uget(v_bs_1996_, v_i_1995_);
                    v___x_1999_ = lean_unsigned_to_nat(0);
                    v_bs_x27_2000_ = lean_array_uset(v_bs_1996_, v_i_1995_, v___x_1999_);
                    v___x_2001_ = lean_box(0);
                    lean_inc_ref(v_f_1993_);
                    v___x_2002_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0(v_f_1993_, v___x_2001_, v_v_1998_);
                    v___x_2003_ = 1usize;
                    v___x_2004_ = lean_usize_add(v_i_1995_, v___x_2003_);
                    v___x_2005_ = lean_array_uset(v_bs_x27_2000_, v_i_1995_, v___x_2002_);
                    v_i_1995_ = v___x_2004_;
                    v_bs_1996_ = v___x_2005_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1___boxed(
    mut v_f_2007_: *mut LeanObject,
    mut v_sz_2008_: *mut LeanObject,
    mut v_i_2009_: *mut LeanObject,
    mut v_bs_2010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2011_: usize = 0;
    let mut v_i_boxed_2012_: usize = 0;
    let mut v_res_2013_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2011_ = lean_unbox_usize(v_sz_2008_);
    lean_dec(v_sz_2008_);
    v_i_boxed_2012_ = lean_unbox_usize(v_i_2009_);
    lean_dec(v_i_2009_);
    v_res_2013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(v_f_2007_, v_sz_boxed_2011_, v_i_boxed_2012_, v_bs_2010_);
    return v_res_2013_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(
    mut v_as_2014_: *mut LeanObject,
    mut v_i_2015_: usize,
    mut v_stop_2016_: usize,
    mut v_b_2017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2018_: u8 = 0;
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: usize = 0;
    let mut v___x_2023_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2018_ = lean_usize_dec_eq(v_i_2015_, v_stop_2016_);
                if v___x_2018_ == 0 {
                    v___x_2019_ = lean_array_uget_borrowed(v_as_2014_, v_i_2015_);
                    v___x_2020_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v___x_2019_);
                    v___x_2021_ = lean_nat_add(v_b_2017_, v___x_2020_);
                    lean_dec(v___x_2020_);
                    lean_dec(v_b_2017_);
                    v___x_2022_ = 1usize;
                    v___x_2023_ = lean_usize_add(v_i_2015_, v___x_2022_);
                    v_i_2015_ = v___x_2023_;
                    v_b_2017_ = v___x_2021_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2017_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2___boxed(
    mut v_as_2025_: *mut LeanObject,
    mut v_i_2026_: *mut LeanObject,
    mut v_stop_2027_: *mut LeanObject,
    mut v_b_2028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2029_: usize = 0;
    let mut v_stop_boxed_2030_: usize = 0;
    let mut v_res_2031_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2029_ = lean_unbox_usize(v_i_2026_);
    lean_dec(v_i_2026_);
    v_stop_boxed_2030_ = lean_unbox_usize(v_stop_2027_);
    lean_dec(v_stop_2027_);
    v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(v_as_2025_, v_i_boxed_2029_, v_stop_boxed_2030_, v_b_2028_);
    lean_dec_ref(v_as_2025_);
    return v_res_2031_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0(
    mut v_f_2032_: *mut LeanObject,
    mut v_m_2033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2037_: u8 = 0;
    let mut v_sz_2038_: usize = 0;
    let mut v___x_2039_: usize = 0;
    let mut v_newBuckets_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: u8 = 0;
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: u8 = 0;
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: usize = 0;
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: usize = 0;
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2061_: u8 = 0;
    let mut v_unused_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2034_ = lean_ctor_get(v_m_2033_, 1);
                v_isSharedCheck_2061_ = (!lean_is_exclusive(v_m_2033_)) as u8;
                if v_isSharedCheck_2061_ == 0 {
                    v_unused_2062_ = lean_ctor_get(v_m_2033_, 0);
                    lean_dec(v_unused_2062_);
                    v___x_2036_ = v_m_2033_;
                    v_isShared_2037_ = v_isSharedCheck_2061_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_2034_);
                    lean_dec(v_m_2033_);
                    v___x_2036_ = lean_box(0);
                    v_isShared_2037_ = v_isSharedCheck_2061_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_sz_2038_ = lean_array_size(v_buckets_2034_);
                v___x_2039_ = 0usize;
                v_newBuckets_2040_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(v_f_2032_, v_sz_2038_, v___x_2039_, v_buckets_2034_);
                v___x_2041_ = lean_unsigned_to_nat(0);
                v___x_2042_ = lean_array_get_size(v_newBuckets_2040_);
                v___x_2043_ = lean_nat_dec_lt(v___x_2041_, v___x_2042_);
                if v___x_2043_ == 0 {
                    if v_isShared_2037_ == 0 {
                        lean_ctor_set(v___x_2036_, 1, v_newBuckets_2040_);
                        lean_ctor_set(v___x_2036_, 0, v___x_2041_);
                        v___x_2045_ = v___x_2036_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2041_);
                        lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_newBuckets_2040_);
                        v___x_2045_ = v_reuseFailAlloc_2046_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2047_ = lean_nat_dec_le(v___x_2042_, v___x_2042_);
                    if v___x_2047_ == 0 {
                        if v___x_2043_ == 0 {
                            if v_isShared_2037_ == 0 {
                                lean_ctor_set(v___x_2036_, 1, v_newBuckets_2040_);
                                lean_ctor_set(v___x_2036_, 0, v___x_2041_);
                                v___x_2049_ = v___x_2036_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2041_);
                                lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_newBuckets_2040_);
                                v___x_2049_ = v_reuseFailAlloc_2050_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v___x_2051_ = lean_usize_of_nat(v___x_2042_);
                            v___x_2052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(v_newBuckets_2040_, v___x_2039_, v___x_2051_, v___x_2041_);
                            if v_isShared_2037_ == 0 {
                                lean_ctor_set(v___x_2036_, 1, v_newBuckets_2040_);
                                lean_ctor_set(v___x_2036_, 0, v___x_2052_);
                                v___x_2054_ = v___x_2036_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
                                lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_newBuckets_2040_);
                                v___x_2054_ = v_reuseFailAlloc_2055_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v___x_2056_ = lean_usize_of_nat(v___x_2042_);
                        v___x_2057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(v_newBuckets_2040_, v___x_2039_, v___x_2056_, v___x_2041_);
                        if v_isShared_2037_ == 0 {
                            lean_ctor_set(v___x_2036_, 1, v_newBuckets_2040_);
                            lean_ctor_set(v___x_2036_, 0, v___x_2057_);
                            v___x_2059_ = v___x_2036_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
                            lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_newBuckets_2040_);
                            v___x_2059_ = v_reuseFailAlloc_2060_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2045_;
            }
            3 => {
                return v___x_2049_;
            }
            4 => {
                return v___x_2054_;
            }
            5 => {
                return v___x_2059_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_NameHashSet_filter(
    mut v_f_2063_: *mut LeanObject,
    mut v_s_2064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    v___x_2065_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0(
        v_f_2063_, v_s_2064_,
    );
    return v___x_2065_;
}
pub unsafe fn l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(
    mut v_x_2066_: *mut LeanObject,
    mut v_x_2067_: *mut LeanObject,
) -> u8 {
    let mut v___x_2068_: u8 = 0;
    let mut v___x_2069_: u8 = 0;
    let mut v___x_2070_: u8 = 0;
    let mut v_head_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2066_) == 0 {
                    if lean_obj_tag(v_x_2067_) == 0 {
                        v___x_2068_ = 1;
                        return v___x_2068_;
                    } else {
                        v___x_2069_ = 0;
                        return v___x_2069_;
                    }
                } else {
                    if lean_obj_tag(v_x_2067_) == 0 {
                        v___x_2070_ = 0;
                        return v___x_2070_;
                    } else {
                        v_head_2071_ = lean_ctor_get(v_x_2066_, 0);
                        v_tail_2072_ = lean_ctor_get(v_x_2066_, 1);
                        v_head_2073_ = lean_ctor_get(v_x_2067_, 0);
                        v_tail_2074_ = lean_ctor_get(v_x_2067_, 1);
                        v___x_2075_ = lean_nat_dec_eq(v_head_2071_, v_head_2073_);
                        if v___x_2075_ == 0 {
                            return v___x_2075_;
                        } else {
                            v_x_2066_ = v_tail_2072_;
                            v_x_2067_ = v_tail_2074_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0___boxed(
    mut v_x_2077_: *mut LeanObject,
    mut v_x_2078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2079_: u8 = 0;
    let mut v_r_2080_: *mut LeanObject = core::ptr::null_mut();
    v_res_2079_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(v_x_2077_, v_x_2078_);
    lean_dec(v_x_2078_);
    lean_dec(v_x_2077_);
    v_r_2080_ = lean_box((v_res_2079_) as usize);
    return v_r_2080_;
}
pub unsafe fn l_Lean_MacroScopesView_isPrefixOf(
    mut v_v_u2081_2081_: *mut LeanObject,
    mut v_v_u2082_2082_: *mut LeanObject,
) -> u8 {
    let mut v_name_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imported_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imported_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2092_: u8 = 0;
    let mut v___x_2093_: u8 = 0;
    let mut v___x_2094_: u8 = 0;
    let mut v___x_2095_: u8 = 0;
    let mut v___x_2096_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2083_ = lean_ctor_get(v_v_u2081_2081_, 0);
                v_imported_2084_ = lean_ctor_get(v_v_u2081_2081_, 1);
                v_ctx_2085_ = lean_ctor_get(v_v_u2081_2081_, 2);
                v_scopes_2086_ = lean_ctor_get(v_v_u2081_2081_, 3);
                v_name_2087_ = lean_ctor_get(v_v_u2082_2082_, 0);
                v_imported_2088_ = lean_ctor_get(v_v_u2082_2082_, 1);
                v_ctx_2089_ = lean_ctor_get(v_v_u2082_2082_, 2);
                v_scopes_2090_ = lean_ctor_get(v_v_u2082_2082_, 3);
                v___x_2095_ = l_Lean_Name_isPrefixOf(v_name_2083_, v_name_2087_);
                if v___x_2095_ == 0 {
                    v___y_2092_ = v___x_2095_;
                    state = 1;
                    continue;
                } else {
                    v___x_2096_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(
                        v_scopes_2086_,
                        v_scopes_2090_,
                    );
                    v___y_2092_ = v___x_2096_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_2092_ == 0 {
                    return v___y_2092_;
                } else {
                    v___x_2093_ = lean_name_eq(v_ctx_2085_, v_ctx_2089_);
                    if v___x_2093_ == 0 {
                        return v___x_2093_;
                    } else {
                        v___x_2094_ = lean_name_eq(v_imported_2084_, v_imported_2088_);
                        return v___x_2094_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MacroScopesView_isPrefixOf___boxed(
    mut v_v_u2081_2097_: *mut LeanObject,
    mut v_v_u2082_2098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2099_: u8 = 0;
    let mut v_r_2100_: *mut LeanObject = core::ptr::null_mut();
    v_res_2099_ = l_Lean_MacroScopesView_isPrefixOf(v_v_u2081_2097_, v_v_u2082_2098_);
    lean_dec_ref(v_v_u2082_2098_);
    lean_dec_ref(v_v_u2081_2097_);
    v_r_2100_ = lean_box((v_res_2099_) as usize);
    return v_r_2100_;
}
pub unsafe fn l_Lean_MacroScopesView_isSuffixOf(
    mut v_v_u2081_2101_: *mut LeanObject,
    mut v_v_u2082_2102_: *mut LeanObject,
) -> u8 {
    let mut v_name_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imported_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imported_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2112_: u8 = 0;
    let mut v___x_2113_: u8 = 0;
    let mut v___x_2114_: u8 = 0;
    let mut v___x_2115_: u8 = 0;
    let mut v___x_2116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2103_ = lean_ctor_get(v_v_u2081_2101_, 0);
                v_imported_2104_ = lean_ctor_get(v_v_u2081_2101_, 1);
                v_ctx_2105_ = lean_ctor_get(v_v_u2081_2101_, 2);
                v_scopes_2106_ = lean_ctor_get(v_v_u2081_2101_, 3);
                v_name_2107_ = lean_ctor_get(v_v_u2082_2102_, 0);
                v_imported_2108_ = lean_ctor_get(v_v_u2082_2102_, 1);
                v_ctx_2109_ = lean_ctor_get(v_v_u2082_2102_, 2);
                v_scopes_2110_ = lean_ctor_get(v_v_u2082_2102_, 3);
                v___x_2115_ = l_Lean_Name_isSuffixOf(v_name_2103_, v_name_2107_);
                if v___x_2115_ == 0 {
                    v___y_2112_ = v___x_2115_;
                    state = 1;
                    continue;
                } else {
                    v___x_2116_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(
                        v_scopes_2106_,
                        v_scopes_2110_,
                    );
                    v___y_2112_ = v___x_2116_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_2112_ == 0 {
                    return v___y_2112_;
                } else {
                    v___x_2113_ = lean_name_eq(v_ctx_2105_, v_ctx_2109_);
                    if v___x_2113_ == 0 {
                        return v___x_2113_;
                    } else {
                        v___x_2114_ = lean_name_eq(v_imported_2104_, v_imported_2108_);
                        return v___x_2114_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MacroScopesView_isSuffixOf___boxed(
    mut v_v_u2081_2117_: *mut LeanObject,
    mut v_v_u2082_2118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2119_: u8 = 0;
    let mut v_r_2120_: *mut LeanObject = core::ptr::null_mut();
    v_res_2119_ = l_Lean_MacroScopesView_isSuffixOf(v_v_u2081_2117_, v_v_u2082_2118_);
    lean_dec_ref(v_v_u2082_2118_);
    lean_dec_ref(v_v_u2081_2117_);
    v_r_2120_ = lean_box((v_res_2119_) as usize);
    return v_r_2120_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_NameMap_Basic(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Std_Data_TreeSet_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_SSet(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_NameSet_empty = _init_l_Lean_NameSet_empty();
    lean_mark_persistent(l_Lean_NameSet_empty);
    l_Lean_NameSet_instEmptyCollection = _init_l_Lean_NameSet_instEmptyCollection();
    lean_mark_persistent(l_Lean_NameSet_instEmptyCollection);
    l_Lean_NameSet_instInhabited = _init_l_Lean_NameSet_instInhabited();
    lean_mark_persistent(l_Lean_NameSet_instInhabited);
    l_Lean_NameSSet_empty = _init_l_Lean_NameSSet_empty();
    lean_mark_persistent(l_Lean_NameSSet_empty);
    l_Lean_NameSSet_instEmptyCollection = _init_l_Lean_NameSSet_instEmptyCollection();
    lean_mark_persistent(l_Lean_NameSSet_instEmptyCollection);
    l_Lean_NameSSet_instInhabited = _init_l_Lean_NameSSet_instInhabited();
    lean_mark_persistent(l_Lean_NameSSet_instInhabited);
    l_Lean_NameHashSet_empty = _init_l_Lean_NameHashSet_empty();
    lean_mark_persistent(l_Lean_NameHashSet_empty);
    l_Lean_NameHashSet_instEmptyCollection = _init_l_Lean_NameHashSet_instEmptyCollection();
    lean_mark_persistent(l_Lean_NameHashSet_instEmptyCollection);
    l_Lean_NameHashSet_instInhabited = _init_l_Lean_NameHashSet_instInhabited();
    lean_mark_persistent(l_Lean_NameHashSet_instInhabited);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_NameMap_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_NameMap_Basic(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Std_Data_TreeSet_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_SSet(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_NameMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_NameMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_NameMap_Basic(builtin);
}
