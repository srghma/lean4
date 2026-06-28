// Lean compiler output
// Module: Lean.Meta.DiscrTree.Util
// Imports: Lean.Meta.DiscrTree.Basic
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_foldl___redArg, l_Lean_PersistentHashMap_foldlMAux___redArg,
    l_Lean_PersistentHashMap_mapM___redArg,
};
use crate::r#gen::Lean::Meta::DiscrTree::Basic::{
    initialize_Lean_Meta_DiscrTree_Basic, runtime_initialize_Lean_Meta_DiscrTree_Basic,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__0_value: LeanClosureObject<0> =
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
static mut l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__1_value: LeanClosureObject<0> =
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
static mut l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__2_value: LeanClosureObject<0> =
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
static mut l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__3_value: LeanClosureObject<0> =
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
static mut l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__4_value: LeanClosureObject<0> =
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
static mut l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__5_value: LeanClosureObject<0> =
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
static mut l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__6_value: LeanClosureObject<0> =
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
static mut l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__7_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__8_value: LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_values___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_DiscrTree_values___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_DiscrTree_values___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_values___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_values___redArg___closed__1_value: LeanArrayObject<0> =
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
static mut l_Lean_Meta_DiscrTree_values___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_values___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_values___redArg___closed__2_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_DiscrTree_values___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_values___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_values___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_values___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_toArray___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_DiscrTree_toArray___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_DiscrTree_toArray___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_toArray___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_toArray___redArg___closed__1_value: LeanArrayObject<0> =
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
static mut l_Lean_Meta_DiscrTree_toArray___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_toArray___redArg___closed__2_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_DiscrTree_toArray___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_DiscrTree_toArray___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_DiscrTree_toArray___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_size___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_DiscrTree_size___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_DiscrTree_size___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_size___redArg___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1(
    mut v_children_787_: *mut LeanObject,
    mut v___x_788_: *mut LeanObject,
    mut v_toApplicative_789_: *mut LeanObject,
    mut v_inst_790_: *mut LeanObject,
    mut v___f_791_: *mut LeanObject,
    mut v_s_792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: u8 = 0;
    v___x_793_ = lean_array_get_size(v_children_787_);
    v___x_794_ = lean_nat_dec_lt(v___x_788_, v___x_793_);
    if v___x_794_ == 0 {
        let mut v_toPure_795_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_791_);
        lean_dec_ref(v_inst_790_);
        lean_dec_ref(v_children_787_);
        v_toPure_795_ = lean_ctor_get(v_toApplicative_789_, 1);
        lean_inc(v_toPure_795_);
        lean_dec_ref(v_toApplicative_789_);
        v___x_796_ = lean_apply_2(v_toPure_795_, lean_box(0), v_s_792_);
        return v___x_796_;
    } else {
        let mut v___x_797_: u8 = 0;
        v___x_797_ = lean_nat_dec_le(v___x_793_, v___x_793_);
        if v___x_797_ == 0 {
            if v___x_794_ == 0 {
                let mut v_toPure_798_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___f_791_);
                lean_dec_ref(v_inst_790_);
                lean_dec_ref(v_children_787_);
                v_toPure_798_ = lean_ctor_get(v_toApplicative_789_, 1);
                lean_inc(v_toPure_798_);
                lean_dec_ref(v_toApplicative_789_);
                v___x_799_ = lean_apply_2(v_toPure_798_, lean_box(0), v_s_792_);
                return v___x_799_;
            } else {
                let mut v___x_800_: usize = 0;
                let mut v___x_801_: usize = 0;
                let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_toApplicative_789_);
                v___x_800_ = 0usize;
                v___x_801_ = lean_usize_of_nat(v___x_793_);
                v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_790_,
                    v___f_791_,
                    v_children_787_,
                    v___x_800_,
                    v___x_801_,
                    v_s_792_,
                );
                return v___x_802_;
            }
        } else {
            let mut v___x_803_: usize = 0;
            let mut v___x_804_: usize = 0;
            let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_toApplicative_789_);
            v___x_803_ = 0usize;
            v___x_804_ = lean_usize_of_nat(v___x_793_);
            v___x_805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v_inst_790_,
                v___f_791_,
                v_children_787_,
                v___x_803_,
                v___x_804_,
                v_s_792_,
            );
            return v___x_805_;
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1___boxed(
    mut v_children_806_: *mut LeanObject,
    mut v___x_807_: *mut LeanObject,
    mut v_toApplicative_808_: *mut LeanObject,
    mut v_inst_809_: *mut LeanObject,
    mut v___f_810_: *mut LeanObject,
    mut v_s_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_812_: *mut LeanObject = core::ptr::null_mut();
    v_res_812_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1(
        v_children_806_,
        v___x_807_,
        v_toApplicative_808_,
        v_inst_809_,
        v___f_810_,
        v_s_811_,
    );
    lean_dec(v___x_807_);
    return v_res_812_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__2(
    mut v_f_813_: *mut LeanObject,
    mut v_initialKeys_814_: *mut LeanObject,
    mut v_s_815_: *mut LeanObject,
    mut v_v_816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    v___x_817_ = lean_apply_3(v_f_813_, v_s_815_, v_initialKeys_814_, v_v_816_);
    return v___x_817_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_foldM___redArg(
    mut v_inst_818_: *mut LeanObject,
    mut v_initialKeys_819_: *mut LeanObject,
    mut v_f_820_: *mut LeanObject,
    mut v_x_821_: *mut LeanObject,
    mut v_x_822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: u8 = 0;
    v_toApplicative_823_ = lean_ctor_get(v_inst_818_, 0);
    v_toBind_824_ = lean_ctor_get(v_inst_818_, 1);
    lean_inc(v_toBind_824_);
    v_vs_825_ = lean_ctor_get(v_x_822_, 0);
    lean_inc_ref(v_vs_825_);
    v_children_826_ = lean_ctor_get(v_x_822_, 1);
    lean_inc_ref(v_children_826_);
    lean_dec_ref(v_x_822_);
    lean_inc(v_f_820_);
    lean_inc_ref_n(v_inst_818_, 2);
    lean_inc_ref(v_initialKeys_819_);
    v___f_827_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_827_, 0, v_initialKeys_819_);
    lean_closure_set(v___f_827_, 1, v_inst_818_);
    lean_closure_set(v___f_827_, 2, v_f_820_);
    v___x_828_ = lean_unsigned_to_nat(0);
    lean_inc_ref(v_toApplicative_823_);
    v___f_829_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_829_, 0, v_children_826_);
    lean_closure_set(v___f_829_, 1, v___x_828_);
    lean_closure_set(v___f_829_, 2, v_toApplicative_823_);
    lean_closure_set(v___f_829_, 3, v_inst_818_);
    lean_closure_set(v___f_829_, 4, v___f_827_);
    v___x_830_ = lean_array_get_size(v_vs_825_);
    v___x_831_ = lean_nat_dec_lt(v___x_828_, v___x_830_);
    if v___x_831_ == 0 {
        let mut v_toPure_832_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_toApplicative_823_);
        lean_dec_ref(v_vs_825_);
        lean_dec(v_f_820_);
        lean_dec_ref(v_initialKeys_819_);
        lean_dec_ref(v_inst_818_);
        v_toPure_832_ = lean_ctor_get(v_toApplicative_823_, 1);
        lean_inc(v_toPure_832_);
        lean_dec_ref(v_toApplicative_823_);
        v___x_833_ = lean_apply_2(v_toPure_832_, lean_box(0), v_x_821_);
        v___x_834_ = lean_apply_4(
            v_toBind_824_,
            lean_box(0),
            lean_box(0),
            v___x_833_,
            v___f_829_,
        );
        return v___x_834_;
    } else {
        let mut v___f_835_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_836_: u8 = 0;
        v___f_835_ = lean_alloc_closure(
            l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__2 as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_835_, 0, v_f_820_);
        lean_closure_set(v___f_835_, 1, v_initialKeys_819_);
        v___x_836_ = lean_nat_dec_le(v___x_830_, v___x_830_);
        if v___x_836_ == 0 {
            if v___x_831_ == 0 {
                let mut v_toPure_837_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
                lean_inc_ref(v_toApplicative_823_);
                lean_dec_ref(v___f_835_);
                lean_dec_ref(v_vs_825_);
                lean_dec_ref(v_inst_818_);
                v_toPure_837_ = lean_ctor_get(v_toApplicative_823_, 1);
                lean_inc(v_toPure_837_);
                lean_dec_ref(v_toApplicative_823_);
                v___x_838_ = lean_apply_2(v_toPure_837_, lean_box(0), v_x_821_);
                v___x_839_ = lean_apply_4(
                    v_toBind_824_,
                    lean_box(0),
                    lean_box(0),
                    v___x_838_,
                    v___f_829_,
                );
                return v___x_839_;
            } else {
                let mut v___x_840_: usize = 0;
                let mut v___x_841_: usize = 0;
                let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
                v___x_840_ = 0usize;
                v___x_841_ = lean_usize_of_nat(v___x_830_);
                v___x_842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_818_,
                    v___f_835_,
                    v_vs_825_,
                    v___x_840_,
                    v___x_841_,
                    v_x_821_,
                );
                v___x_843_ = lean_apply_4(
                    v_toBind_824_,
                    lean_box(0),
                    lean_box(0),
                    v___x_842_,
                    v___f_829_,
                );
                return v___x_843_;
            }
        } else {
            let mut v___x_844_: usize = 0;
            let mut v___x_845_: usize = 0;
            let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
            v___x_844_ = 0usize;
            v___x_845_ = lean_usize_of_nat(v___x_830_);
            v___x_846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v_inst_818_,
                v___f_835_,
                v_vs_825_,
                v___x_844_,
                v___x_845_,
                v_x_821_,
            );
            v___x_847_ = lean_apply_4(
                v_toBind_824_,
                lean_box(0),
                lean_box(0),
                v___x_846_,
                v___f_829_,
            );
            return v___x_847_;
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__0(
    mut v_initialKeys_848_: *mut LeanObject,
    mut v_inst_849_: *mut LeanObject,
    mut v_f_850_: *mut LeanObject,
    mut v_s_851_: *mut LeanObject,
    mut v_x_852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    v_fst_853_ = lean_ctor_get(v_x_852_, 0);
    lean_inc(v_fst_853_);
    v_snd_854_ = lean_ctor_get(v_x_852_, 1);
    lean_inc(v_snd_854_);
    lean_dec_ref(v_x_852_);
    v___x_855_ = lean_array_push(v_initialKeys_848_, v_fst_853_);
    v___x_856_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(
        v_inst_849_,
        v___x_855_,
        v_f_850_,
        v_s_851_,
        v_snd_854_,
    );
    return v___x_856_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_foldM(
    mut v_m_857_: *mut LeanObject,
    mut v_00_u03c3_858_: *mut LeanObject,
    mut v_00_u03b1_859_: *mut LeanObject,
    mut v_inst_860_: *mut LeanObject,
    mut v_initialKeys_861_: *mut LeanObject,
    mut v_f_862_: *mut LeanObject,
    mut v_x_863_: *mut LeanObject,
    mut v_x_864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    v___x_865_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(
        v_inst_860_,
        v_initialKeys_861_,
        v_f_862_,
        v_x_863_,
        v_x_864_,
    );
    return v___x_865_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0(
    mut v_f_866_: *mut LeanObject,
    mut v_s_867_: *mut LeanObject,
    mut v_k_868_: *mut LeanObject,
    mut v_a_869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    v___x_870_ = lean_apply_3(v_f_866_, v_s_867_, v_k_868_, v_a_869_);
    return v___x_870_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_fold___redArg(
    mut v_initialKeys_890_: *mut LeanObject,
    mut v_f_891_: *mut LeanObject,
    mut v_init_892_: *mut LeanObject,
    mut v_t_893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    v___f_894_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_894_, 0, v_f_891_);
    v___x_895_ = l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9;
    v___x_896_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(
        v___x_895_,
        v_initialKeys_890_,
        v___f_894_,
        v_init_892_,
        v_t_893_,
    );
    return v___x_896_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_fold(
    mut v_00_u03c3_897_: *mut LeanObject,
    mut v_00_u03b1_898_: *mut LeanObject,
    mut v_initialKeys_899_: *mut LeanObject,
    mut v_f_900_: *mut LeanObject,
    mut v_init_901_: *mut LeanObject,
    mut v_t_902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    v___f_903_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_903_, 0, v_f_900_);
    v___x_904_ = l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9;
    v___x_905_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(
        v___x_904_,
        v_initialKeys_899_,
        v___f_903_,
        v_init_901_,
        v_t_902_,
    );
    return v___x_905_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(
    mut v_inst_906_: *mut LeanObject,
    mut v_f_907_: *mut LeanObject,
    mut v_x_908_: *mut LeanObject,
    mut v_x_909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: u8 = 0;
    v_toApplicative_910_ = lean_ctor_get(v_inst_906_, 0);
    v_toBind_911_ = lean_ctor_get(v_inst_906_, 1);
    lean_inc(v_toBind_911_);
    v_vs_912_ = lean_ctor_get(v_x_909_, 0);
    lean_inc_ref(v_vs_912_);
    v_children_913_ = lean_ctor_get(v_x_909_, 1);
    lean_inc_ref(v_children_913_);
    lean_dec_ref(v_x_909_);
    lean_inc(v_f_907_);
    lean_inc_ref_n(v_inst_906_, 2);
    v___f_914_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_914_, 0, v_inst_906_);
    lean_closure_set(v___f_914_, 1, v_f_907_);
    v___x_915_ = lean_unsigned_to_nat(0);
    lean_inc_ref(v_toApplicative_910_);
    v___f_916_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_916_, 0, v_children_913_);
    lean_closure_set(v___f_916_, 1, v___x_915_);
    lean_closure_set(v___f_916_, 2, v_toApplicative_910_);
    lean_closure_set(v___f_916_, 3, v_inst_906_);
    lean_closure_set(v___f_916_, 4, v___f_914_);
    v___x_917_ = lean_array_get_size(v_vs_912_);
    v___x_918_ = lean_nat_dec_lt(v___x_915_, v___x_917_);
    if v___x_918_ == 0 {
        let mut v_toPure_919_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_toApplicative_910_);
        lean_dec_ref(v_vs_912_);
        lean_dec(v_f_907_);
        lean_dec_ref(v_inst_906_);
        v_toPure_919_ = lean_ctor_get(v_toApplicative_910_, 1);
        lean_inc(v_toPure_919_);
        lean_dec_ref(v_toApplicative_910_);
        v___x_920_ = lean_apply_2(v_toPure_919_, lean_box(0), v_x_908_);
        v___x_921_ = lean_apply_4(
            v_toBind_911_,
            lean_box(0),
            lean_box(0),
            v___x_920_,
            v___f_916_,
        );
        return v___x_921_;
    } else {
        let mut v___x_922_: u8 = 0;
        v___x_922_ = lean_nat_dec_le(v___x_917_, v___x_917_);
        if v___x_922_ == 0 {
            if v___x_918_ == 0 {
                let mut v_toPure_923_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
                lean_inc_ref(v_toApplicative_910_);
                lean_dec_ref(v_vs_912_);
                lean_dec(v_f_907_);
                lean_dec_ref(v_inst_906_);
                v_toPure_923_ = lean_ctor_get(v_toApplicative_910_, 1);
                lean_inc(v_toPure_923_);
                lean_dec_ref(v_toApplicative_910_);
                v___x_924_ = lean_apply_2(v_toPure_923_, lean_box(0), v_x_908_);
                v___x_925_ = lean_apply_4(
                    v_toBind_911_,
                    lean_box(0),
                    lean_box(0),
                    v___x_924_,
                    v___f_916_,
                );
                return v___x_925_;
            } else {
                let mut v___x_926_: usize = 0;
                let mut v___x_927_: usize = 0;
                let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
                v___x_926_ = 0usize;
                v___x_927_ = lean_usize_of_nat(v___x_917_);
                v___x_928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_906_,
                    v_f_907_,
                    v_vs_912_,
                    v___x_926_,
                    v___x_927_,
                    v_x_908_,
                );
                v___x_929_ = lean_apply_4(
                    v_toBind_911_,
                    lean_box(0),
                    lean_box(0),
                    v___x_928_,
                    v___f_916_,
                );
                return v___x_929_;
            }
        } else {
            let mut v___x_930_: usize = 0;
            let mut v___x_931_: usize = 0;
            let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
            v___x_930_ = 0usize;
            v___x_931_ = lean_usize_of_nat(v___x_917_);
            v___x_932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v_inst_906_,
                v_f_907_,
                v_vs_912_,
                v___x_930_,
                v___x_931_,
                v_x_908_,
            );
            v___x_933_ = lean_apply_4(
                v_toBind_911_,
                lean_box(0),
                lean_box(0),
                v___x_932_,
                v___f_916_,
            );
            return v___x_933_;
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__0(
    mut v_inst_934_: *mut LeanObject,
    mut v_f_935_: *mut LeanObject,
    mut v_s_936_: *mut LeanObject,
    mut v_x_937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    v_snd_938_ = lean_ctor_get(v_x_937_, 1);
    lean_inc(v_snd_938_);
    lean_dec_ref(v_x_937_);
    v___x_939_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(
        v_inst_934_,
        v_f_935_,
        v_s_936_,
        v_snd_938_,
    );
    return v___x_939_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_foldValuesM(
    mut v_m_940_: *mut LeanObject,
    mut v_00_u03c3_941_: *mut LeanObject,
    mut v_00_u03b1_942_: *mut LeanObject,
    mut v_inst_943_: *mut LeanObject,
    mut v_f_944_: *mut LeanObject,
    mut v_x_945_: *mut LeanObject,
    mut v_x_946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    v___x_947_ =
        l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_943_, v_f_944_, v_x_945_, v_x_946_);
    return v___x_947_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0(
    mut v_f_948_: *mut LeanObject,
    mut v_x1_949_: *mut LeanObject,
    mut v_x2_950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    v___x_951_ = lean_apply_2(v_f_948_, v_x1_949_, v_x2_950_);
    return v___x_951_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_foldValues___redArg(
    mut v_f_952_: *mut LeanObject,
    mut v_init_953_: *mut LeanObject,
    mut v_t_954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    v___f_955_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_955_, 0, v_f_952_);
    v___x_956_ = l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9;
    v___x_957_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(
        v___x_956_,
        v___f_955_,
        v_init_953_,
        v_t_954_,
    );
    return v___x_957_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_foldValues(
    mut v_00_u03c3_958_: *mut LeanObject,
    mut v_00_u03b1_959_: *mut LeanObject,
    mut v_f_960_: *mut LeanObject,
    mut v_init_961_: *mut LeanObject,
    mut v_t_962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    v___f_963_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_963_, 0, v_f_960_);
    v___x_964_ = l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9;
    v___x_965_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(
        v___x_964_,
        v___f_963_,
        v_init_961_,
        v_t_962_,
    );
    return v___x_965_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_size___redArg(
    mut v_x_966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vs_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: u8 = 0;
    v_vs_967_ = lean_ctor_get(v_x_966_, 0);
    v_children_968_ = lean_ctor_get(v_x_966_, 1);
    v___x_969_ = lean_array_get_size(v_vs_967_);
    v___x_970_ = lean_unsigned_to_nat(0);
    v___x_971_ = lean_array_get_size(v_children_968_);
    v___x_972_ = lean_nat_dec_lt(v___x_970_, v___x_971_);
    if v___x_972_ == 0 {
        return v___x_969_;
    } else {
        let mut v___x_973_: u8 = 0;
        v___x_973_ = lean_nat_dec_le(v___x_971_, v___x_971_);
        if v___x_973_ == 0 {
            if v___x_972_ == 0 {
                return v___x_969_;
            } else {
                let mut v___x_974_: usize = 0;
                let mut v___x_975_: usize = 0;
                let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
                v___x_974_ = 0usize;
                v___x_975_ = lean_usize_of_nat(v___x_971_);
                v___x_976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_children_968_, v___x_974_, v___x_975_, v___x_969_);
                return v___x_976_;
            }
        } else {
            let mut v___x_977_: usize = 0;
            let mut v___x_978_: usize = 0;
            let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
            v___x_977_ = 0usize;
            v___x_978_ = lean_usize_of_nat(v___x_971_);
            v___x_979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_children_968_, v___x_977_, v___x_978_, v___x_969_);
            return v___x_979_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(
    mut v_as_980_: *mut LeanObject,
    mut v_i_981_: usize,
    mut v_stop_982_: usize,
    mut v_b_983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_984_: u8 = 0;
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: usize = 0;
    let mut v___x_990_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_984_ = lean_usize_dec_eq(v_i_981_, v_stop_982_);
                if v___x_984_ == 0 {
                    v___x_985_ = lean_array_uget_borrowed(v_as_980_, v_i_981_);
                    v_snd_986_ = lean_ctor_get(v___x_985_, 1);
                    v___x_987_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_snd_986_);
                    v___x_988_ = lean_nat_add(v_b_983_, v___x_987_);
                    lean_dec(v___x_987_);
                    lean_dec(v_b_983_);
                    v___x_989_ = 1usize;
                    v___x_990_ = lean_usize_add(v_i_981_, v___x_989_);
                    v_i_981_ = v___x_990_;
                    v_b_983_ = v___x_988_;
                    state = 0;
                    continue;
                } else {
                    return v_b_983_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg___boxed(
    mut v_as_992_: *mut LeanObject,
    mut v_i_993_: *mut LeanObject,
    mut v_stop_994_: *mut LeanObject,
    mut v_b_995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_996_: usize = 0;
    let mut v_stop_boxed_997_: usize = 0;
    let mut v_res_998_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_996_ = lean_unbox_usize(v_i_993_);
    lean_dec(v_i_993_);
    v_stop_boxed_997_ = lean_unbox_usize(v_stop_994_);
    lean_dec(v_stop_994_);
    v_res_998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_as_992_, v_i_boxed_996_, v_stop_boxed_997_, v_b_995_);
    lean_dec_ref(v_as_992_);
    return v_res_998_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_size___redArg___boxed(
    mut v_x_999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1000_: *mut LeanObject = core::ptr::null_mut();
    v_res_1000_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_x_999_);
    lean_dec_ref(v_x_999_);
    return v_res_1000_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_size(
    mut v_00_u03b1_1001_: *mut LeanObject,
    mut v_x_1002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    v___x_1003_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_x_1002_);
    return v___x_1003_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_size___boxed(
    mut v_00_u03b1_1004_: *mut LeanObject,
    mut v_x_1005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1006_: *mut LeanObject = core::ptr::null_mut();
    v_res_1006_ = l_Lean_Meta_DiscrTree_Trie_size(v_00_u03b1_1004_, v_x_1005_);
    lean_dec_ref(v_x_1005_);
    return v_res_1006_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0(
    mut v_00_u03b1_1007_: *mut LeanObject,
    mut v_as_1008_: *mut LeanObject,
    mut v_i_1009_: usize,
    mut v_stop_1010_: usize,
    mut v_b_1011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    v___x_1012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_as_1008_, v_i_1009_, v_stop_1010_, v_b_1011_);
    return v___x_1012_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___boxed(
    mut v_00_u03b1_1013_: *mut LeanObject,
    mut v_as_1014_: *mut LeanObject,
    mut v_i_1015_: *mut LeanObject,
    mut v_stop_1016_: *mut LeanObject,
    mut v_b_1017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1018_: usize = 0;
    let mut v_stop_boxed_1019_: usize = 0;
    let mut v_res_1020_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1018_ = lean_unbox_usize(v_i_1015_);
    lean_dec(v_i_1015_);
    v_stop_boxed_1019_ = lean_unbox_usize(v_stop_1016_);
    lean_dec(v_stop_1016_);
    v_res_1020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0(v_00_u03b1_1013_, v_as_1014_, v_i_boxed_1018_, v_stop_boxed_1019_, v_b_1017_);
    lean_dec_ref(v_as_1014_);
    return v_res_1020_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_foldM___redArg___lam__0(
    mut v_inst_1021_: *mut LeanObject,
    mut v_f_1022_: *mut LeanObject,
    mut v_s_1023_: *mut LeanObject,
    mut v_k_1024_: *mut LeanObject,
    mut v_t_1025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    v___x_1026_ = lean_unsigned_to_nat(1);
    v___x_1027_ = lean_mk_empty_array_with_capacity(v___x_1026_);
    v___x_1028_ = lean_array_push(v___x_1027_, v_k_1024_);
    v___x_1029_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(
        v_inst_1021_,
        v___x_1028_,
        v_f_1022_,
        v_s_1023_,
        v_t_1025_,
    );
    return v___x_1029_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_foldM___redArg(
    mut v_inst_1030_: *mut LeanObject,
    mut v_f_1031_: *mut LeanObject,
    mut v_init_1032_: *mut LeanObject,
    mut v_t_1033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_1030_);
    v___f_1034_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_foldM___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_1034_, 0, v_inst_1030_);
    lean_closure_set(v___f_1034_, 1, v_f_1031_);
    v___x_1035_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v_inst_1030_,
        v___f_1034_,
        v_t_1033_,
        v_init_1032_,
    );
    return v___x_1035_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_foldM(
    mut v_m_1036_: *mut LeanObject,
    mut v_00_u03c3_1037_: *mut LeanObject,
    mut v_00_u03b1_1038_: *mut LeanObject,
    mut v_inst_1039_: *mut LeanObject,
    mut v_f_1040_: *mut LeanObject,
    mut v_init_1041_: *mut LeanObject,
    mut v_t_1042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_1039_);
    v___f_1043_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_foldM___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_1043_, 0, v_inst_1039_);
    lean_closure_set(v___f_1043_, 1, v_f_1040_);
    v___x_1044_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v_inst_1039_,
        v___f_1043_,
        v_t_1042_,
        v_init_1041_,
    );
    return v___x_1044_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_fold___redArg___lam__0(
    mut v_f_1045_: *mut LeanObject,
    mut v_s_1046_: *mut LeanObject,
    mut v_keys_1047_: *mut LeanObject,
    mut v_a_1048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    v___x_1049_ = lean_apply_3(v_f_1045_, v_s_1046_, v_keys_1047_, v_a_1048_);
    return v___x_1049_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_fold___redArg___lam__1(
    mut v___x_1050_: *mut LeanObject,
    mut v___f_1051_: *mut LeanObject,
    mut v_s_1052_: *mut LeanObject,
    mut v_k_1053_: *mut LeanObject,
    mut v_t_1054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    v___x_1055_ = lean_unsigned_to_nat(1);
    v___x_1056_ = lean_mk_empty_array_with_capacity(v___x_1055_);
    v___x_1057_ = lean_array_push(v___x_1056_, v_k_1053_);
    v___x_1058_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(
        v___x_1050_,
        v___x_1057_,
        v___f_1051_,
        v_s_1052_,
        v_t_1054_,
    );
    return v___x_1058_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_fold___redArg(
    mut v_f_1059_: *mut LeanObject,
    mut v_init_1060_: *mut LeanObject,
    mut v_t_1061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    v___f_1062_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_fold___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1062_, 0, v_f_1059_);
    v___x_1063_ = l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9;
    v___f_1064_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_fold___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_1064_, 0, v___x_1063_);
    lean_closure_set(v___f_1064_, 1, v___f_1062_);
    v___x_1065_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v___x_1063_,
        v___f_1064_,
        v_t_1061_,
        v_init_1060_,
    );
    return v___x_1065_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_fold(
    mut v_00_u03c3_1066_: *mut LeanObject,
    mut v_00_u03b1_1067_: *mut LeanObject,
    mut v_f_1068_: *mut LeanObject,
    mut v_init_1069_: *mut LeanObject,
    mut v_t_1070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    v___f_1071_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_fold___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1071_, 0, v_f_1068_);
    v___x_1072_ = l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9;
    v___f_1073_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_fold___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_1073_, 0, v___x_1072_);
    lean_closure_set(v___f_1073_, 1, v___f_1071_);
    v___x_1074_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v___x_1072_,
        v___f_1073_,
        v_t_1070_,
        v_init_1069_,
    );
    return v___x_1074_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(
    mut v_inst_1075_: *mut LeanObject,
    mut v_f_1076_: *mut LeanObject,
    mut v_s_1077_: *mut LeanObject,
    mut v_x_1078_: *mut LeanObject,
    mut v_t_1079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    v___x_1080_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(
        v_inst_1075_,
        v_f_1076_,
        v_s_1077_,
        v_t_1079_,
    );
    return v___x_1080_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed(
    mut v_inst_1081_: *mut LeanObject,
    mut v_f_1082_: *mut LeanObject,
    mut v_s_1083_: *mut LeanObject,
    mut v_x_1084_: *mut LeanObject,
    mut v_t_1085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1086_: *mut LeanObject = core::ptr::null_mut();
    v_res_1086_ = l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(
        v_inst_1081_,
        v_f_1082_,
        v_s_1083_,
        v_x_1084_,
        v_t_1085_,
    );
    lean_dec(v_x_1084_);
    return v_res_1086_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_foldValuesM___redArg(
    mut v_inst_1087_: *mut LeanObject,
    mut v_f_1088_: *mut LeanObject,
    mut v_init_1089_: *mut LeanObject,
    mut v_t_1090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_1087_);
    v___f_1091_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_1091_, 0, v_inst_1087_);
    lean_closure_set(v___f_1091_, 1, v_f_1088_);
    v___x_1092_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v_inst_1087_,
        v___f_1091_,
        v_t_1090_,
        v_init_1089_,
    );
    return v___x_1092_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_foldValuesM(
    mut v_m_1093_: *mut LeanObject,
    mut v_00_u03c3_1094_: *mut LeanObject,
    mut v_00_u03b1_1095_: *mut LeanObject,
    mut v_inst_1096_: *mut LeanObject,
    mut v_f_1097_: *mut LeanObject,
    mut v_init_1098_: *mut LeanObject,
    mut v_t_1099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_1096_);
    v___f_1100_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_1100_, 0, v_inst_1096_);
    lean_closure_set(v___f_1100_, 1, v_f_1097_);
    v___x_1101_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v_inst_1096_,
        v___f_1100_,
        v_t_1099_,
        v_init_1098_,
    );
    return v___x_1101_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(
    mut v___x_1102_: *mut LeanObject,
    mut v___f_1103_: *mut LeanObject,
    mut v_s_1104_: *mut LeanObject,
    mut v_x_1105_: *mut LeanObject,
    mut v_t_1106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    v___x_1107_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(
        v___x_1102_,
        v___f_1103_,
        v_s_1104_,
        v_t_1106_,
    );
    return v___x_1107_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed(
    mut v___x_1108_: *mut LeanObject,
    mut v___f_1109_: *mut LeanObject,
    mut v_s_1110_: *mut LeanObject,
    mut v_x_1111_: *mut LeanObject,
    mut v_t_1112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1113_: *mut LeanObject = core::ptr::null_mut();
    v_res_1113_ = l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(
        v___x_1108_,
        v___f_1109_,
        v_s_1110_,
        v_x_1111_,
        v_t_1112_,
    );
    lean_dec(v_x_1111_);
    return v_res_1113_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_foldValues___redArg(
    mut v_f_1114_: *mut LeanObject,
    mut v_init_1115_: *mut LeanObject,
    mut v_t_1116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    v___f_1117_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1117_, 0, v_f_1114_);
    v___x_1118_ = l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9;
    v___f_1119_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_1119_, 0, v___x_1118_);
    lean_closure_set(v___f_1119_, 1, v___f_1117_);
    v___x_1120_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v___x_1118_,
        v___f_1119_,
        v_t_1116_,
        v_init_1115_,
    );
    return v___x_1120_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_foldValues(
    mut v_00_u03c3_1121_: *mut LeanObject,
    mut v_00_u03b1_1122_: *mut LeanObject,
    mut v_f_1123_: *mut LeanObject,
    mut v_init_1124_: *mut LeanObject,
    mut v_t_1125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    v___f_1126_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1126_, 0, v_f_1123_);
    v___x_1127_ = l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9;
    v___f_1128_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_1128_, 0, v___x_1127_);
    lean_closure_set(v___f_1128_, 1, v___f_1126_);
    v___x_1129_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v___x_1127_,
        v___f_1128_,
        v_t_1125_,
        v_init_1124_,
    );
    return v___x_1129_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(
    mut v_f_1130_: *mut LeanObject,
    mut v_x1_1131_: u8,
    mut v_x2_1132_: *mut LeanObject,
) -> u8 {
    if v_x1_1131_ == 0 {
        let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1134_: u8 = 0;
        v___x_1133_ = lean_apply_1(v_f_1130_, v_x2_1132_);
        v___x_1134_ = (lean_unbox(v___x_1133_) as u8);
        return v___x_1134_;
    } else {
        lean_dec(v_x2_1132_);
        lean_dec_ref(v_f_1130_);
        return v_x1_1131_;
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed(
    mut v_f_1135_: *mut LeanObject,
    mut v_x1_1136_: *mut LeanObject,
    mut v_x2_1137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x1_82__boxed_1138_: u8 = 0;
    let mut v_res_1139_: u8 = 0;
    let mut v_r_1140_: *mut LeanObject = core::ptr::null_mut();
    v_x1_82__boxed_1138_ = (lean_unbox(v_x1_1136_) as u8);
    v_res_1139_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(
        v_f_1135_,
        v_x1_82__boxed_1138_,
        v_x2_1137_,
    );
    v_r_1140_ = lean_box((v_res_1139_) as usize);
    return v_r_1140_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(
    mut v___x_1141_: *mut LeanObject,
    mut v___f_1142_: *mut LeanObject,
    mut v_s_1143_: u8,
    mut v_x_1144_: *mut LeanObject,
    mut v_t_1145_: *mut LeanObject,
) -> u8 {
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: u8 = 0;
    v___x_1146_ = lean_box((v_s_1143_) as usize);
    v___x_1147_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(
        v___x_1141_,
        v___f_1142_,
        v___x_1146_,
        v_t_1145_,
    );
    v___x_1148_ = (lean_unbox(v___x_1147_) as u8);
    lean_dec(v___x_1147_);
    return v___x_1148_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed(
    mut v___x_1149_: *mut LeanObject,
    mut v___f_1150_: *mut LeanObject,
    mut v_s_1151_: *mut LeanObject,
    mut v_x_1152_: *mut LeanObject,
    mut v_t_1153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_boxed_1154_: u8 = 0;
    let mut v_res_1155_: u8 = 0;
    let mut v_r_1156_: *mut LeanObject = core::ptr::null_mut();
    v_s_boxed_1154_ = (lean_unbox(v_s_1151_) as u8);
    v_res_1155_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(
        v___x_1149_,
        v___f_1150_,
        v_s_boxed_1154_,
        v_x_1152_,
        v_t_1153_,
    );
    lean_dec(v_x_1152_);
    v_r_1156_ = lean_box((v_res_1155_) as usize);
    return v_r_1156_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_containsValueP___redArg(
    mut v_t_1157_: *mut LeanObject,
    mut v_f_1158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: u8 = 0;
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    v___f_1159_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1159_, 0, v_f_1158_);
    v___x_1160_ = 0;
    v___x_1161_ = l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9;
    v___f_1162_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_1162_, 0, v___x_1161_);
    lean_closure_set(v___f_1162_, 1, v___f_1159_);
    v___x_1163_ = lean_box((v___x_1160_) as usize);
    v___x_1164_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v___x_1161_,
        v___f_1162_,
        v_t_1157_,
        v___x_1163_,
    );
    return v___x_1164_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_containsValueP(
    mut v_00_u03b1_1165_: *mut LeanObject,
    mut v_t_1166_: *mut LeanObject,
    mut v_f_1167_: *mut LeanObject,
) -> u8 {
    let mut v___f_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: u8 = 0;
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: u8 = 0;
    v___f_1168_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1168_, 0, v_f_1167_);
    v___x_1169_ = 0;
    v___x_1170_ = l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9;
    v___f_1171_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_1171_, 0, v___x_1170_);
    lean_closure_set(v___f_1171_, 1, v___f_1168_);
    v___x_1172_ = lean_box((v___x_1169_) as usize);
    v___x_1173_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v___x_1170_,
        v___f_1171_,
        v_t_1166_,
        v___x_1172_,
    );
    v___x_1174_ = (lean_unbox(v___x_1173_) as u8);
    lean_dec(v___x_1173_);
    return v___x_1174_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_containsValueP___boxed(
    mut v_00_u03b1_1175_: *mut LeanObject,
    mut v_t_1176_: *mut LeanObject,
    mut v_f_1177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1178_: u8 = 0;
    let mut v_r_1179_: *mut LeanObject = core::ptr::null_mut();
    v_res_1178_ = l_Lean_Meta_DiscrTree_containsValueP(v_00_u03b1_1175_, v_t_1176_, v_f_1177_);
    v_r_1179_ = lean_box((v_res_1178_) as usize);
    return v_r_1179_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_values___redArg___lam__0(
    mut v_x1_1180_: *mut LeanObject,
    mut v_x2_1181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    v___x_1182_ = lean_array_push(v_x1_1180_, v_x2_1181_);
    return v___x_1182_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_values___redArg___lam__1(
    mut v___x_1183_: *mut LeanObject,
    mut v___f_1184_: *mut LeanObject,
    mut v_s_1185_: *mut LeanObject,
    mut v_x_1186_: *mut LeanObject,
    mut v_t_1187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    v___x_1188_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(
        v___x_1183_,
        v___f_1184_,
        v_s_1185_,
        v_t_1187_,
    );
    return v___x_1188_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_values___redArg___lam__1___boxed(
    mut v___x_1189_: *mut LeanObject,
    mut v___f_1190_: *mut LeanObject,
    mut v_s_1191_: *mut LeanObject,
    mut v_x_1192_: *mut LeanObject,
    mut v_t_1193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1194_: *mut LeanObject = core::ptr::null_mut();
    v_res_1194_ = l_Lean_Meta_DiscrTree_values___redArg___lam__1(
        v___x_1189_,
        v___f_1190_,
        v_s_1191_,
        v_x_1192_,
        v_t_1193_,
    );
    lean_dec(v_x_1192_);
    return v_res_1194_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_values___redArg(
    mut v_t_1201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    v___x_1202_ = l_Lean_Meta_DiscrTree_values___redArg___closed__1;
    v___x_1203_ = l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9;
    v___f_1204_ = l_Lean_Meta_DiscrTree_values___redArg___closed__2;
    v___x_1205_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v___x_1203_,
        v___f_1204_,
        v_t_1201_,
        v___x_1202_,
    );
    return v___x_1205_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_values(
    mut v_00_u03b1_1206_: *mut LeanObject,
    mut v_t_1207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    v___x_1208_ = l_Lean_Meta_DiscrTree_values___redArg___closed__1;
    v___x_1209_ = l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9;
    v___f_1210_ = l_Lean_Meta_DiscrTree_values___redArg___closed__2;
    v___x_1211_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v___x_1209_,
        v___f_1210_,
        v_t_1207_,
        v___x_1208_,
    );
    return v___x_1211_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_toArray___redArg___lam__0(
    mut v_s_1212_: *mut LeanObject,
    mut v_keys_1213_: *mut LeanObject,
    mut v_a_1214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    v___x_1215_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1215_, 0, v_keys_1213_);
    lean_ctor_set(v___x_1215_, 1, v_a_1214_);
    v___x_1216_ = lean_array_push(v_s_1212_, v___x_1215_);
    return v___x_1216_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_toArray___redArg___lam__1(
    mut v___x_1217_: *mut LeanObject,
    mut v___f_1218_: *mut LeanObject,
    mut v_s_1219_: *mut LeanObject,
    mut v_k_1220_: *mut LeanObject,
    mut v_t_1221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    v___x_1222_ = lean_unsigned_to_nat(1);
    v___x_1223_ = lean_mk_empty_array_with_capacity(v___x_1222_);
    v___x_1224_ = lean_array_push(v___x_1223_, v_k_1220_);
    v___x_1225_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(
        v___x_1217_,
        v___x_1224_,
        v___f_1218_,
        v_s_1219_,
        v_t_1221_,
    );
    return v___x_1225_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_toArray___redArg(
    mut v_t_1232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    v___x_1233_ = l_Lean_Meta_DiscrTree_toArray___redArg___closed__1;
    v___x_1234_ = l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9;
    v___f_1235_ = l_Lean_Meta_DiscrTree_toArray___redArg___closed__2;
    v___x_1236_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v___x_1234_,
        v___f_1235_,
        v_t_1232_,
        v___x_1233_,
    );
    return v___x_1236_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_toArray(
    mut v_00_u03b1_1237_: *mut LeanObject,
    mut v_t_1238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    v___x_1239_ = l_Lean_Meta_DiscrTree_toArray___redArg___closed__1;
    v___x_1240_ = l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9;
    v___f_1241_ = l_Lean_Meta_DiscrTree_toArray___redArg___closed__2;
    v___x_1242_ = l_Lean_PersistentHashMap_foldlMAux___redArg(
        v___x_1240_,
        v___f_1241_,
        v_t_1238_,
        v___x_1239_,
    );
    return v___x_1242_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_size___redArg___lam__0(
    mut v_n_1243_: *mut LeanObject,
    mut v_x_1244_: *mut LeanObject,
    mut v_t_1245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    v___x_1246_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_t_1245_);
    v___x_1247_ = lean_nat_add(v_n_1243_, v___x_1246_);
    lean_dec(v___x_1246_);
    return v___x_1247_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_size___redArg___lam__0___boxed(
    mut v_n_1248_: *mut LeanObject,
    mut v_x_1249_: *mut LeanObject,
    mut v_t_1250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1251_: *mut LeanObject = core::ptr::null_mut();
    v_res_1251_ = l_Lean_Meta_DiscrTree_size___redArg___lam__0(v_n_1248_, v_x_1249_, v_t_1250_);
    lean_dec_ref(v_t_1250_);
    lean_dec(v_x_1249_);
    lean_dec(v_n_1248_);
    return v_res_1251_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_size___redArg(
    mut v_t_1253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    v___f_1254_ = l_Lean_Meta_DiscrTree_size___redArg___closed__0;
    v___x_1255_ = lean_unsigned_to_nat(0);
    v___x_1256_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_1253_, v___f_1254_, v___x_1255_);
    return v___x_1256_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_size(
    mut v_00_u03b1_1257_: *mut LeanObject,
    mut v_t_1258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    v___f_1259_ = l_Lean_Meta_DiscrTree_size___redArg___closed__0;
    v___x_1260_ = lean_unsigned_to_nat(0);
    v___x_1261_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_1258_, v___f_1259_, v___x_1260_);
    return v___x_1261_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0(
    mut v_fst_1262_: *mut LeanObject,
    mut v_toPure_1263_: *mut LeanObject,
    mut v_____do__lift_1264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    v___x_1265_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1265_, 0, v_fst_1262_);
    lean_ctor_set(v___x_1265_, 1, v_____do__lift_1264_);
    v___x_1266_ = lean_apply_2(v_toPure_1263_, lean_box(0), v___x_1265_);
    return v___x_1266_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2(
    mut v_____do__lift_1267_: *mut LeanObject,
    mut v_toPure_1268_: *mut LeanObject,
    mut v_____do__lift_1269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    v___x_1270_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1270_, 0, v_____do__lift_1267_);
    lean_ctor_set(v___x_1270_, 1, v_____do__lift_1269_);
    v___x_1271_ = lean_apply_2(v_toPure_1268_, lean_box(0), v___x_1270_);
    return v___x_1271_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3(
    mut v_toPure_1272_: *mut LeanObject,
    mut v_children_1273_: *mut LeanObject,
    mut v_inst_1274_: *mut LeanObject,
    mut v___f_1275_: *mut LeanObject,
    mut v_toBind_1276_: *mut LeanObject,
    mut v_____do__lift_1277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1279_: usize = 0;
    let mut v___x_1280_: usize = 0;
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    v___f_1278_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1278_, 0, v_____do__lift_1277_);
    lean_closure_set(v___f_1278_, 1, v_toPure_1272_);
    v_sz_1279_ = lean_array_size(v_children_1273_);
    v___x_1280_ = 0usize;
    v___x_1281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_inst_1274_,
        v___f_1275_,
        v_sz_1279_,
        v___x_1280_,
        v_children_1273_,
    );
    v___x_1282_ = lean_apply_4(
        v_toBind_1276_,
        lean_box(0),
        lean_box(0),
        v___x_1281_,
        v___f_1278_,
    );
    return v___x_1282_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(
    mut v_inst_1283_: *mut LeanObject,
    mut v_t_1284_: *mut LeanObject,
    mut v_f_1285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1286_ = lean_ctor_get(v_inst_1283_, 0);
    v_toBind_1287_ = lean_ctor_get(v_inst_1283_, 1);
    lean_inc_n(v_toBind_1287_, 3);
    v_toPure_1288_ = lean_ctor_get(v_toApplicative_1286_, 1);
    lean_inc_n(v_toPure_1288_, 2);
    v_vs_1289_ = lean_ctor_get(v_t_1284_, 0);
    lean_inc_ref(v_vs_1289_);
    v_children_1290_ = lean_ctor_get(v_t_1284_, 1);
    lean_inc_ref(v_children_1290_);
    lean_dec_ref(v_t_1284_);
    lean_inc(v_f_1285_);
    lean_inc_ref(v_inst_1283_);
    v___f_1291_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_1291_, 0, v_toPure_1288_);
    lean_closure_set(v___f_1291_, 1, v_inst_1283_);
    lean_closure_set(v___f_1291_, 2, v_f_1285_);
    lean_closure_set(v___f_1291_, 3, v_toBind_1287_);
    v___f_1292_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_1292_, 0, v_toPure_1288_);
    lean_closure_set(v___f_1292_, 1, v_children_1290_);
    lean_closure_set(v___f_1292_, 2, v_inst_1283_);
    lean_closure_set(v___f_1292_, 3, v___f_1291_);
    lean_closure_set(v___f_1292_, 4, v_toBind_1287_);
    v___x_1293_ = lean_apply_1(v_f_1285_, v_vs_1289_);
    v___x_1294_ = lean_apply_4(
        v_toBind_1287_,
        lean_box(0),
        lean_box(0),
        v___x_1293_,
        v___f_1292_,
    );
    return v___x_1294_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1(
    mut v_toPure_1295_: *mut LeanObject,
    mut v_inst_1296_: *mut LeanObject,
    mut v_f_1297_: *mut LeanObject,
    mut v_toBind_1298_: *mut LeanObject,
    mut v_x_1299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1300_ = lean_ctor_get(v_x_1299_, 0);
    lean_inc(v_fst_1300_);
    v_snd_1301_ = lean_ctor_get(v_x_1299_, 1);
    lean_inc(v_snd_1301_);
    lean_dec_ref(v_x_1299_);
    v___f_1302_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1302_, 0, v_fst_1300_);
    lean_closure_set(v___f_1302_, 1, v_toPure_1295_);
    v___x_1303_ =
        l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_1296_, v_snd_1301_, v_f_1297_);
    v___x_1304_ = lean_apply_4(
        v_toBind_1298_,
        lean_box(0),
        lean_box(0),
        v___x_1303_,
        v___f_1302_,
    );
    return v___x_1304_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_mapArraysM(
    mut v_m_1305_: *mut LeanObject,
    mut v_inst_1306_: *mut LeanObject,
    mut v_00_u03b1_1307_: *mut LeanObject,
    mut v_00_u03b2_1308_: *mut LeanObject,
    mut v_t_1309_: *mut LeanObject,
    mut v_f_1310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    v___x_1311_ =
        l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_1306_, v_t_1309_, v_f_1310_);
    return v___x_1311_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0(
    mut v_inst_1312_: *mut LeanObject,
    mut v_f_1313_: *mut LeanObject,
    mut v_t_1314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    v___x_1315_ =
        l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_1312_, v_t_1314_, v_f_1313_);
    return v___x_1315_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1(
    mut v_toPure_1316_: *mut LeanObject,
    mut v_____do__lift_1317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    v___x_1318_ = lean_apply_2(v_toPure_1316_, lean_box(0), v_____do__lift_1317_);
    return v___x_1318_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_mapArraysM___redArg(
    mut v_inst_1319_: *mut LeanObject,
    mut v_d_1320_: *mut LeanObject,
    mut v_f_1321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1322_ = lean_ctor_get(v_inst_1319_, 0);
    v_toBind_1323_ = lean_ctor_get(v_inst_1319_, 1);
    lean_inc(v_toBind_1323_);
    v_toPure_1324_ = lean_ctor_get(v_toApplicative_1322_, 1);
    lean_inc_ref(v_inst_1319_);
    v___f_1325_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1325_, 0, v_inst_1319_);
    lean_closure_set(v___f_1325_, 1, v_f_1321_);
    lean_inc(v_toPure_1324_);
    v___f_1326_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1326_, 0, v_toPure_1324_);
    v___x_1327_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_1319_, v_d_1320_, v___f_1325_);
    v___x_1328_ = lean_apply_4(
        v_toBind_1323_,
        lean_box(0),
        lean_box(0),
        v___x_1327_,
        v___f_1326_,
    );
    return v___x_1328_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_mapArraysM(
    mut v_m_1329_: *mut LeanObject,
    mut v_inst_1330_: *mut LeanObject,
    mut v_00_u03b1_1331_: *mut LeanObject,
    mut v_00_u03b2_1332_: *mut LeanObject,
    mut v_d_1333_: *mut LeanObject,
    mut v_f_1334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    v___x_1335_ = l_Lean_Meta_DiscrTree_mapArraysM___redArg(v_inst_1330_, v_d_1333_, v_f_1334_);
    return v___x_1335_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0(
    mut v_f_1336_: *mut LeanObject,
    mut v_A_1337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    v___x_1338_ = lean_apply_1(v_f_1336_, v_A_1337_);
    return v___x_1338_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___redArg(
    mut v_f_1339_: *mut LeanObject,
    mut v_sz_1340_: usize,
    mut v_i_1341_: usize,
    mut v_bs_1342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1343_: u8 = 0;
    let mut v_v_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1349_: u8 = 0;
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: usize = 0;
    let mut v___x_1356_: usize = 0;
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1360_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1343_ = lean_usize_dec_lt(v_i_1341_, v_sz_1340_);
                if v___x_1343_ == 0 {
                    lean_dec_ref(v_f_1339_);
                    return v_bs_1342_;
                } else {
                    v_v_1344_ = lean_array_uget(v_bs_1342_, v_i_1341_);
                    v_fst_1345_ = lean_ctor_get(v_v_1344_, 0);
                    v_snd_1346_ = lean_ctor_get(v_v_1344_, 1);
                    v_isSharedCheck_1360_ = (!lean_is_exclusive(v_v_1344_)) as u8;
                    if v_isSharedCheck_1360_ == 0 {
                        v___x_1348_ = v_v_1344_;
                        v_isShared_1349_ = v_isSharedCheck_1360_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1346_);
                        lean_inc(v_fst_1345_);
                        lean_dec(v_v_1344_);
                        v___x_1348_ = lean_box(0);
                        v_isShared_1349_ = v_isSharedCheck_1360_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1350_ = lean_unsigned_to_nat(0);
                v_bs_x27_1351_ = lean_array_uset(v_bs_1342_, v_i_1341_, v___x_1350_);
                lean_inc_ref(v_f_1339_);
                v___x_1352_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0___redArg(v_snd_1346_, v_f_1339_);
                if v_isShared_1349_ == 0 {
                    lean_ctor_set(v___x_1348_, 1, v___x_1352_);
                    v___x_1354_ = v___x_1348_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_fst_1345_);
                    lean_ctor_set(v_reuseFailAlloc_1359_, 1, v___x_1352_);
                    v___x_1354_ = v_reuseFailAlloc_1359_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1355_ = 1usize;
                v___x_1356_ = lean_usize_add(v_i_1341_, v___x_1355_);
                v___x_1357_ = lean_array_uset(v_bs_x27_1351_, v_i_1341_, v___x_1354_);
                v_i_1341_ = v___x_1356_;
                v_bs_1342_ = v___x_1357_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0___redArg(
    mut v_t_1361_: *mut LeanObject,
    mut v_f_1362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vs_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1367_: u8 = 0;
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1369_: usize = 0;
    let mut v___x_1370_: usize = 0;
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1375_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vs_1363_ = lean_ctor_get(v_t_1361_, 0);
                v_children_1364_ = lean_ctor_get(v_t_1361_, 1);
                v_isSharedCheck_1375_ = (!lean_is_exclusive(v_t_1361_)) as u8;
                if v_isSharedCheck_1375_ == 0 {
                    v___x_1366_ = v_t_1361_;
                    v_isShared_1367_ = v_isSharedCheck_1375_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_children_1364_);
                    lean_inc(v_vs_1363_);
                    lean_dec(v_t_1361_);
                    v___x_1366_ = lean_box(0);
                    v_isShared_1367_ = v_isSharedCheck_1375_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_f_1362_);
                v___x_1368_ = lean_apply_1(v_f_1362_, v_vs_1363_);
                v_sz_1369_ = lean_array_size(v_children_1364_);
                v___x_1370_ = 0usize;
                v___x_1371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___redArg(v_f_1362_, v_sz_1369_, v___x_1370_, v_children_1364_);
                if v_isShared_1367_ == 0 {
                    lean_ctor_set(v___x_1366_, 1, v___x_1371_);
                    lean_ctor_set(v___x_1366_, 0, v___x_1368_);
                    v___x_1373_ = v___x_1366_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1368_);
                    lean_ctor_set(v_reuseFailAlloc_1374_, 1, v___x_1371_);
                    v___x_1373_ = v_reuseFailAlloc_1374_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1373_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_f_1376_: *mut LeanObject,
    mut v_sz_1377_: *mut LeanObject,
    mut v_i_1378_: *mut LeanObject,
    mut v_bs_1379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1380_: usize = 0;
    let mut v_i_boxed_1381_: usize = 0;
    let mut v_res_1382_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1380_ = lean_unbox_usize(v_sz_1377_);
    lean_dec(v_sz_1377_);
    v_i_boxed_1381_ = lean_unbox_usize(v_i_1378_);
    lean_dec(v_i_1378_);
    v_res_1382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___redArg(v_f_1376_, v_sz_boxed_1380_, v_i_boxed_1381_, v_bs_1379_);
    return v_res_1382_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0___redArg___lam__0(
    mut v_f_1383_: *mut LeanObject,
    mut v_t_1384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    v___x_1385_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0___redArg(v_t_1384_, v_f_1383_);
    return v___x_1385_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(
    mut v_f_1386_: *mut LeanObject,
    mut v_as_1387_: *mut LeanObject,
    mut v_i_1388_: *mut LeanObject,
    mut v_acc_1389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: u8 = 0;
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1390_ = lean_array_get_size(v_as_1387_);
                v___x_1391_ = lean_nat_dec_eq(v_i_1388_, v___x_1390_);
                if v___x_1391_ == 0 {
                    v___x_1392_ = lean_array_fget_borrowed(v_as_1387_, v_i_1388_);
                    lean_inc(v_f_1386_);
                    lean_inc(v___x_1392_);
                    v___x_1393_ = lean_apply_1(v_f_1386_, v___x_1392_);
                    v___x_1394_ = lean_unsigned_to_nat(1);
                    v___x_1395_ = lean_nat_add(v_i_1388_, v___x_1394_);
                    lean_dec(v_i_1388_);
                    v___x_1396_ = lean_array_push(v_acc_1389_, v___x_1393_);
                    v_i_1388_ = v___x_1395_;
                    v_acc_1389_ = v___x_1396_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_i_1388_);
                    lean_dec(v_f_1386_);
                    return v_acc_1389_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___boxed(
    mut v_f_1398_: *mut LeanObject,
    mut v_as_1399_: *mut LeanObject,
    mut v_i_1400_: *mut LeanObject,
    mut v_acc_1401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1402_: *mut LeanObject = core::ptr::null_mut();
    v_res_1402_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_f_1398_, v_as_1399_, v_i_1400_, v_acc_1401_);
    lean_dec_ref(v_as_1399_);
    return v_res_1402_;
}
pub unsafe fn l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___redArg(
    mut v_f_1403_: *mut LeanObject,
    mut v_as_1404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    v___x_1405_ = lean_unsigned_to_nat(0);
    v___x_1406_ = lean_array_get_size(v_as_1404_);
    v___x_1407_ = lean_mk_empty_array_with_capacity(v___x_1406_);
    v___x_1408_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_f_1403_, v_as_1404_, v___x_1405_, v___x_1407_);
    return v___x_1408_;
}
pub unsafe fn l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___redArg___boxed(
    mut v_f_1409_: *mut LeanObject,
    mut v_as_1410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1411_: *mut LeanObject = core::ptr::null_mut();
    v_res_1411_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___redArg(v_f_1409_, v_as_1410_);
    lean_dec_ref(v_as_1410_);
    return v_res_1411_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___redArg(
    mut v_f_1412_: *mut LeanObject,
    mut v_sz_1413_: usize,
    mut v_i_1414_: usize,
    mut v_bs_1415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1416_: u8 = 0;
    let mut v_v_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: usize = 0;
    let mut v___x_1423_: usize = 0;
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1435_: u8 = 0;
    let mut v_node_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1439_: u8 = 0;
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1444_: u8 = 0;
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1416_ = lean_usize_dec_lt(v_i_1414_, v_sz_1413_);
                if v___x_1416_ == 0 {
                    lean_dec(v_f_1412_);
                    return v_bs_1415_;
                } else {
                    v_v_1417_ = lean_array_uget(v_bs_1415_, v_i_1414_);
                    v___x_1418_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1419_ = lean_array_uset(v_bs_1415_, v_i_1414_, v___x_1418_);
                    match lean_obj_tag(v_v_1417_) {
                        0 => {
                            v_key_1426_ = lean_ctor_get(v_v_1417_, 0);
                            v_val_1427_ = lean_ctor_get(v_v_1417_, 1);
                            v_isSharedCheck_1435_ = (!lean_is_exclusive(v_v_1417_)) as u8;
                            if v_isSharedCheck_1435_ == 0 {
                                v___x_1429_ = v_v_1417_;
                                v_isShared_1430_ = v_isSharedCheck_1435_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_val_1427_);
                                lean_inc(v_key_1426_);
                                lean_dec(v_v_1417_);
                                v___x_1429_ = lean_box(0);
                                v_isShared_1430_ = v_isSharedCheck_1435_;
                                state = 2;
                                continue;
                            }
                        }
                        1 => {
                            v_node_1436_ = lean_ctor_get(v_v_1417_, 0);
                            v_isSharedCheck_1444_ = (!lean_is_exclusive(v_v_1417_)) as u8;
                            if v_isSharedCheck_1444_ == 0 {
                                v___x_1438_ = v_v_1417_;
                                v_isShared_1439_ = v_isSharedCheck_1444_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_node_1436_);
                                lean_dec(v_v_1417_);
                                v___x_1438_ = lean_box(0);
                                v_isShared_1439_ = v_isSharedCheck_1444_;
                                state = 4;
                                continue;
                            }
                        }
                        _ => {
                            v___x_1445_ = lean_box(2);
                            v___y_1421_ = v___x_1445_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1422_ = 1usize;
                v___x_1423_ = lean_usize_add(v_i_1414_, v___x_1422_);
                v___x_1424_ = lean_array_uset(v_bs_x27_1419_, v_i_1414_, v___y_1421_);
                v_i_1414_ = v___x_1423_;
                v_bs_1415_ = v___x_1424_;
                state = 0;
                continue;
            }
            2 => {
                lean_inc(v_f_1412_);
                v___x_1431_ = lean_apply_1(v_f_1412_, v_val_1427_);
                if v_isShared_1430_ == 0 {
                    lean_ctor_set(v___x_1429_, 1, v___x_1431_);
                    v___x_1433_ = v___x_1429_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_key_1426_);
                    lean_ctor_set(v_reuseFailAlloc_1434_, 1, v___x_1431_);
                    v___x_1433_ = v_reuseFailAlloc_1434_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_1421_ = v___x_1433_;
                state = 1;
                continue;
            }
            4 => {
                lean_inc(v_f_1412_);
                v___x_1440_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3___redArg(v_f_1412_, v_node_1436_);
                if v_isShared_1439_ == 0 {
                    lean_ctor_set(v___x_1438_, 0, v___x_1440_);
                    v___x_1442_ = v___x_1438_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
                    v___x_1442_ = v_reuseFailAlloc_1443_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_1421_ = v___x_1442_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3___redArg(
    mut v_f_1446_: *mut LeanObject,
    mut v_n_1447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1451_: u8 = 0;
    let mut v_sz_1452_: usize = 0;
    let mut v___x_1453_: usize = 0;
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1458_: u8 = 0;
    let mut v_ks_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1463_: u8 = 0;
    let mut v_val_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_1447_) == 0 {
                    v_es_1448_ = lean_ctor_get(v_n_1447_, 0);
                    v_isSharedCheck_1458_ = (!lean_is_exclusive(v_n_1447_)) as u8;
                    if v_isSharedCheck_1458_ == 0 {
                        v___x_1450_ = v_n_1447_;
                        v_isShared_1451_ = v_isSharedCheck_1458_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_es_1448_);
                        lean_dec(v_n_1447_);
                        v___x_1450_ = lean_box(0);
                        v_isShared_1451_ = v_isSharedCheck_1458_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_1459_ = lean_ctor_get(v_n_1447_, 0);
                    v_vs_1460_ = lean_ctor_get(v_n_1447_, 1);
                    v_isSharedCheck_1468_ = (!lean_is_exclusive(v_n_1447_)) as u8;
                    if v_isSharedCheck_1468_ == 0 {
                        v___x_1462_ = v_n_1447_;
                        v_isShared_1463_ = v_isSharedCheck_1468_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_vs_1460_);
                        lean_inc(v_ks_1459_);
                        lean_dec(v_n_1447_);
                        v___x_1462_ = lean_box(0);
                        v_isShared_1463_ = v_isSharedCheck_1468_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_1452_ = lean_array_size(v_es_1448_);
                v___x_1453_ = 0usize;
                v___x_1454_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___redArg(v_f_1446_, v_sz_1452_, v___x_1453_, v_es_1448_);
                if v_isShared_1451_ == 0 {
                    lean_ctor_set(v___x_1450_, 0, v___x_1454_);
                    v___x_1456_ = v___x_1450_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
                    v___x_1456_ = v_reuseFailAlloc_1457_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1456_;
            }
            3 => {
                v_val_1464_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___redArg(v_f_1446_, v_vs_1460_);
                lean_dec_ref(v_vs_1460_);
                if v_isShared_1463_ == 0 {
                    lean_ctor_set(v___x_1462_, 1, v_val_1464_);
                    v___x_1466_ = v___x_1462_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_ks_1459_);
                    lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_val_1464_);
                    v___x_1466_ = v_reuseFailAlloc_1467_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___redArg___boxed(
    mut v_f_1469_: *mut LeanObject,
    mut v_sz_1470_: *mut LeanObject,
    mut v_i_1471_: *mut LeanObject,
    mut v_bs_1472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1473_: usize = 0;
    let mut v_i_boxed_1474_: usize = 0;
    let mut v_res_1475_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1473_ = lean_unbox_usize(v_sz_1470_);
    lean_dec(v_sz_1470_);
    v_i_boxed_1474_ = lean_unbox_usize(v_i_1471_);
    lean_dec(v_i_1471_);
    v_res_1475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___redArg(v_f_1469_, v_sz_boxed_1473_, v_i_boxed_1474_, v_bs_1472_);
    return v_res_1475_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0___redArg(
    mut v_d_1476_: *mut LeanObject,
    mut v_f_1477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    v___f_1478_ = lean_alloc_closure(l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_1478_, 0, v_f_1477_);
    v___x_1479_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3___redArg(v___f_1478_, v_d_1476_);
    return v___x_1479_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_mapArrays___redArg(
    mut v_d_1480_: *mut LeanObject,
    mut v_f_1481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    v___f_1482_ = lean_alloc_closure(
        l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1482_, 0, v_f_1481_);
    v___x_1483_ =
        l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0___redArg(
            v_d_1480_,
            v___f_1482_,
        );
    return v___x_1483_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_mapArrays(
    mut v_00_u03b1_1484_: *mut LeanObject,
    mut v_00_u03b2_1485_: *mut LeanObject,
    mut v_d_1486_: *mut LeanObject,
    mut v_f_1487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    v___x_1488_ = l_Lean_Meta_DiscrTree_mapArrays___redArg(v_d_1486_, v_f_1487_);
    return v___x_1488_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0(
    mut v_00_u03b1_1489_: *mut LeanObject,
    mut v_00_u03b2_1490_: *mut LeanObject,
    mut v_d_1491_: *mut LeanObject,
    mut v_f_1492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    v___x_1493_ =
        l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0___redArg(
            v_d_1491_, v_f_1492_,
        );
    return v___x_1493_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0(
    mut v_00_u03b1_1494_: *mut LeanObject,
    mut v_00_u03b2_1495_: *mut LeanObject,
    mut v_t_1496_: *mut LeanObject,
    mut v_f_1497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    v___x_1498_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0___redArg(v_t_1496_, v_f_1497_);
    return v___x_1498_;
}
pub unsafe fn l_Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1___redArg(
    mut v_pm_1499_: *mut LeanObject,
    mut v_f_1500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    v___x_1501_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3___redArg(v_f_1500_, v_pm_1499_);
    return v___x_1501_;
}
pub unsafe fn l_Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1(
    mut v_00_u03b2_1502_: *mut LeanObject,
    mut v_00_u03c3_1503_: *mut LeanObject,
    mut v_pm_1504_: *mut LeanObject,
    mut v_f_1505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    v___x_1506_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3___redArg(v_f_1505_, v_pm_1504_);
    return v___x_1506_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1(
    mut v_00_u03b1_1507_: *mut LeanObject,
    mut v_00_u03b2_1508_: *mut LeanObject,
    mut v_f_1509_: *mut LeanObject,
    mut v_sz_1510_: usize,
    mut v_i_1511_: usize,
    mut v_bs_1512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___redArg(v_f_1509_, v_sz_1510_, v_i_1511_, v_bs_1512_);
    return v___x_1513_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_1514_: *mut LeanObject,
    mut v_00_u03b2_1515_: *mut LeanObject,
    mut v_f_1516_: *mut LeanObject,
    mut v_sz_1517_: *mut LeanObject,
    mut v_i_1518_: *mut LeanObject,
    mut v_bs_1519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1520_: usize = 0;
    let mut v_i_boxed_1521_: usize = 0;
    let mut v_res_1522_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1520_ = lean_unbox_usize(v_sz_1517_);
    lean_dec(v_sz_1517_);
    v_i_boxed_1521_ = lean_unbox_usize(v_i_1518_);
    lean_dec(v_i_1518_);
    v_res_1522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1(v_00_u03b1_1514_, v_00_u03b2_1515_, v_f_1516_, v_sz_boxed_1520_, v_i_boxed_1521_, v_bs_1519_);
    return v_res_1522_;
}
pub unsafe fn l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3(
    mut v_00_u03b1_1523_: *mut LeanObject,
    mut v_00_u03b2_1524_: *mut LeanObject,
    mut v_00_u03c3_1525_: *mut LeanObject,
    mut v_f_1526_: *mut LeanObject,
    mut v_n_1527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    v___x_1528_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3___redArg(v_f_1526_, v_n_1527_);
    return v___x_1528_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4(
    mut v_00_u03b1_1529_: *mut LeanObject,
    mut v_00_u03b2_1530_: *mut LeanObject,
    mut v_00_u03c3_1531_: *mut LeanObject,
    mut v_f_1532_: *mut LeanObject,
    mut v_sz_1533_: usize,
    mut v_i_1534_: usize,
    mut v_bs_1535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    v___x_1536_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___redArg(v_f_1532_, v_sz_1533_, v_i_1534_, v_bs_1535_);
    return v___x_1536_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___boxed(
    mut v_00_u03b1_1537_: *mut LeanObject,
    mut v_00_u03b2_1538_: *mut LeanObject,
    mut v_00_u03c3_1539_: *mut LeanObject,
    mut v_f_1540_: *mut LeanObject,
    mut v_sz_1541_: *mut LeanObject,
    mut v_i_1542_: *mut LeanObject,
    mut v_bs_1543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1544_: usize = 0;
    let mut v_i_boxed_1545_: usize = 0;
    let mut v_res_1546_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1544_ = lean_unbox_usize(v_sz_1541_);
    lean_dec(v_sz_1541_);
    v_i_boxed_1545_ = lean_unbox_usize(v_i_1542_);
    lean_dec(v_i_1542_);
    v_res_1546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4(v_00_u03b1_1537_, v_00_u03b2_1538_, v_00_u03c3_1539_, v_f_1540_, v_sz_boxed_1544_, v_i_boxed_1545_, v_bs_1543_);
    return v_res_1546_;
}
pub unsafe fn l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5(
    mut v_00_u03b1_1547_: *mut LeanObject,
    mut v_00_u03b2_1548_: *mut LeanObject,
    mut v_f_1549_: *mut LeanObject,
    mut v_as_1550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    v___x_1551_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___redArg(v_f_1549_, v_as_1550_);
    return v___x_1551_;
}
pub unsafe fn l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___boxed(
    mut v_00_u03b1_1552_: *mut LeanObject,
    mut v_00_u03b2_1553_: *mut LeanObject,
    mut v_f_1554_: *mut LeanObject,
    mut v_as_1555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1556_: *mut LeanObject = core::ptr::null_mut();
    v_res_1556_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_1552_, v_00_u03b2_1553_, v_f_1554_, v_as_1555_);
    lean_dec_ref(v_as_1555_);
    return v_res_1556_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6(
    mut v_00_u03b1_1557_: *mut LeanObject,
    mut v_00_u03b2_1558_: *mut LeanObject,
    mut v_f_1559_: *mut LeanObject,
    mut v_as_1560_: *mut LeanObject,
    mut v_i_1561_: *mut LeanObject,
    mut v_acc_1562_: *mut LeanObject,
    mut v_hle_1563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    v___x_1564_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_f_1559_, v_as_1560_, v_i_1561_, v_acc_1562_);
    return v___x_1564_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(
    mut v_00_u03b1_1565_: *mut LeanObject,
    mut v_00_u03b2_1566_: *mut LeanObject,
    mut v_f_1567_: *mut LeanObject,
    mut v_as_1568_: *mut LeanObject,
    mut v_i_1569_: *mut LeanObject,
    mut v_acc_1570_: *mut LeanObject,
    mut v_hle_1571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1572_: *mut LeanObject = core::ptr::null_mut();
    v_res_1572_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6(v_00_u03b1_1565_, v_00_u03b2_1566_, v_f_1567_, v_as_1568_, v_i_1569_, v_acc_1570_, v_hle_1571_);
    lean_dec_ref(v_as_1568_);
    return v_res_1572_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_DiscrTree_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_DiscrTree_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_DiscrTree_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_DiscrTree_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_DiscrTree_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_DiscrTree_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_DiscrTree_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_DiscrTree_Util(builtin);
}
