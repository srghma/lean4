// Lean compiler output
// Module: Init.Data.Vector.Basic
// Imports: Init.Data.Array.Nat Init.Data.Array.DecidableEq Init.Data.Range.Polymorphic.RangeIterator Init.Data.Array.InsertIdx Init.Data.Array.MapIdx Init.Data.Range.Polymorphic.Iterators Init.Data.Range.Polymorphic.Nat Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_fswap,
    lean_array_get_borrowed, lean_array_get_size, lean_array_pop, lean_array_push, lean_array_set,
    lean_array_size, lean_array_swap, lean_array_to_list, lean_array_uget_borrowed, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_nat_to_int, lean_string_append, lean_string_length,
    lean_string_utf8_byte_size, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any,
    l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop,
    l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find,
    l___private_Init_Data_Array_Basic_0__Array_firstM_go,
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
    l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_append___redArg,
    l_Array_append___redArg___boxed, l_Array_contains___redArg, l_Array_eraseIdx___redArg,
    l_Array_finIdxOf_x3f___redArg, l_Array_isEqvAux___redArg, l_Array_isPrefixOf___redArg,
    l_Array_mapFinIdxM_map___redArg, l_Array_ofFn___redArg, l_Array_range, l_Array_range_x27,
    l_Array_replace___redArg, l_Array_repr___redArg, l_Array_reverse___redArg,
    l_Array_shrink___redArg, l_Array_unzip___redArg, l_Array_zip___redArg, l_Array_zipIdx___redArg,
    l_Array_zipWithMAux___redArg,
};
use crate::r#gen::Init::Data::Array::DecidableEq::{
    initialize_Init_Data_Array_DecidableEq, l_Array_instDecidableEqImpl___redArg,
    runtime_initialize_Init_Data_Array_DecidableEq,
};
use crate::r#gen::Init::Data::Array::InsertIdx::{
    initialize_Init_Data_Array_InsertIdx, runtime_initialize_Init_Data_Array_InsertIdx,
};
use crate::r#gen::Init::Data::Array::MapIdx::{
    initialize_Init_Data_Array_MapIdx, runtime_initialize_Init_Data_Array_MapIdx,
};
use crate::r#gen::Init::Data::Array::Nat::{
    initialize_Init_Data_Array_Nat, runtime_initialize_Init_Data_Array_Nat,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Nat::{
    initialize_Init_Data_Range_Polymorphic_Nat, runtime_initialize_Init_Data_Range_Polymorphic_Nat,
};
use crate::r#gen::Init::Data::Range::Polymorphic::RangeIterator::{
    initialize_Init_Data_Range_Polymorphic_RangeIterator,
    runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_TSepArray_getElems___redArg, l_Lean_Syntax_mkNumLit,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Array_extract___redArg, l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_Syntax_node5, l_Lean_addMacroScope, l_Lean_mkAtom,
    l_String_toRawSubstring_x27, l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
pub static l_instReprVector_repr___redArg___closed__0_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_instReprVector_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instReprVector_repr___redArg___closed__1_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [116, 111, 65, 114, 114, 97, 121, 0],
    };
static mut l_instReprVector_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_instReprVector_repr___redArg___closed__2_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprVector_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_instReprVector_repr___redArg___closed__3_value: leanh::LeanCtorObject<2> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprVector_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_instReprVector_repr___redArg___closed__4_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_instReprVector_repr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_instReprVector_repr___redArg___closed__5_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprVector_repr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_instReprVector_repr___redArg___closed__6_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprVector_repr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_instReprVector_repr___redArg___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instReprVector_repr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_instReprVector_repr___redArg___closed__8_value: leanh::LeanStringObject<2> =
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
        m_data: [44, 0],
    };
static mut l_instReprVector_repr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_instReprVector_repr___redArg___closed__9_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprVector_repr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_instReprVector_repr___redArg___closed__10_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [115, 105, 122, 101, 95, 116, 111, 65, 114, 114, 97, 121, 0],
    };
static mut l_instReprVector_repr___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_instReprVector_repr___redArg___closed__11_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprVector_repr___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_instReprVector_repr___redArg___closed__12_value: leanh::LeanStringObject<2> =
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
        m_data: [95, 0],
    };
static mut l_instReprVector_repr___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_instReprVector_repr___redArg___closed__13_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprVector_repr___redArg___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_instReprVector_repr___redArg___closed__14_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_instReprVector_repr___redArg___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_instReprVector_repr___redArg___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instReprVector_repr___redArg___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_instReprVector_repr___redArg___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instReprVector_repr___redArg___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_instReprVector_repr___redArg___closed__17_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprVector_repr___redArg___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_instReprVector_repr___redArg___closed__18_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprVector_repr___redArg___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [86, 101, 99, 116, 111, 114, 0],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__1_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [116, 101, 114, 109, 35, 118, 91, 95, 44, 93, 0],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__1_value)
        as *mut leanh::LeanObject;
static l_Vector_term_x23v_x5b___x2c_x5d___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__0_value)
                as *mut leanh::LeanObject,
            2228683986675333841 as *mut leanh::LeanObject,
        ],
    };
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__1_value)
                as *mut leanh::LeanObject,
            13459165728822429150 as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__3_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [97, 110, 100, 116, 104, 101, 110, 0],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__3_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__5_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [35, 118, 91, 0],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__6_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__7_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            119, 105, 116, 104, 111, 117, 116, 80, 111, 115, 105, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__8_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__7_value)
                as *mut leanh::LeanObject,
            1164644006045091397 as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__9_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__10_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__9_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__11_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__10_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__12_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [44, 32, 0],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__13_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__14_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 10,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__11_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instReprVector_repr___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__13_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__15_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__16_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__17_value: leanh::LeanStringObject<2> =
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
        m_data: [93, 0],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__18_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__17_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__19_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__16_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__18_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Vector_term_x23v_x5b___x2c_x5d___closed__20_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__2_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__19_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_term_x23v_x5b___x2c_x5d___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__20_value)
        as *mut leanh::LeanObject;
pub static mut l_Vector_term_x23v_x5b___x2c_x5d: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__3_value) as *mut leanh::LeanObject;
static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__3_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__5_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [86, 101, 99, 116, 111, 114, 46, 109, 107, 0]};
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__5_value) as *mut leanh::LeanObject;
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__7_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__7_value) as *mut leanh::LeanObject;
static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector_term_x23v_x5b___x2c_x5d___closed__0_value) as *mut leanh::LeanObject,2228683986675333841 as *mut leanh::LeanObject] };
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__7_value) as *mut leanh::LeanObject,10967957072707165949 as *mut leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__9_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__10_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8_value) as *mut leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__11_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__10_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__12_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__11_value) as *mut leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__13_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__13_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__15_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [110, 97, 109, 101, 100, 65, 114, 103, 117, 109, 101, 110, 116, 0]};
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__15_value) as *mut leanh::LeanObject;
static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__15_value) as *mut leanh::LeanObject,13594530736035158498 as *mut leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value) as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17_value) as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__18_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [110, 0]};
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__18_value) as *mut leanh::LeanObject;
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__20_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__18_value) as *mut leanh::LeanObject,9980807645604102997 as *mut leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__20_value) as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__21_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__21_value) as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22_value) as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__23_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 35, 91, 95, 44, 93, 0]};
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__23_value) as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__23_value) as *mut leanh::LeanObject,17856333342802343749 as *mut leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24_value) as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__25_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__25_value) as *mut leanh::LeanObject;
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__27_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [114, 102, 108, 0]};
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__27_value) as *mut leanh::LeanObject;
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__29_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__27_value) as *mut leanh::LeanObject,17342663138809293389 as *mut leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__29_value) as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__30_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__29_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__30_value) as *mut leanh::LeanObject;
pub static l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__31_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__30_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__31_value) as *mut leanh::LeanObject;
pub static l_Vector_instGetElemNatLt___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Vector_instGetElemNatLt___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_instGetElemNatLt___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_instGetElemNatLt___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Vector_set___auto__1___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Vector_set___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_set___auto__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Vector_set___auto__1___closed__1_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Vector_set___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_set___auto__1___closed__1_value) as *mut leanh::LeanObject;
static l_Vector_set___auto__1___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Vector_set___auto__1___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector_set___auto__1___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Vector_set___auto__1___closed__2_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_set___auto__1___closed__2_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_set___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Vector_set___auto__1___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_set___auto__1___closed__2_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_set___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8504843326314613972 as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_set___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_set___auto__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Vector_set___auto__1___closed__3_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Vector_set___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_set___auto__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Vector_set___auto__1___closed__4_value: leanh::LeanStringObject<19> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Vector_set___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_set___auto__1___closed__4_value) as *mut leanh::LeanObject;
static l_Vector_set___auto__1___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Vector_set___auto__1___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector_set___auto__1___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Vector_set___auto__1___closed__5_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_set___auto__1___closed__5_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_set___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Vector_set___auto__1___closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_set___auto__1___closed__5_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_set___auto__1___closed__4_value)
                as *mut leanh::LeanObject,
            17228437386856258271 as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_set___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_set___auto__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Vector_set___auto__1___closed__6_value: leanh::LeanStringObject<22> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            116, 97, 99, 116, 105, 99, 71, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116,
            105, 99, 0,
        ],
    };
static mut l_Vector_set___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_set___auto__1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Vector_set___auto__1___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_set___auto__1___closed__6_value)
                as *mut leanh::LeanObject,
            3731765604234633101 as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_set___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_set___auto__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Vector_set___auto__1___closed__8_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            103, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105, 99, 0,
        ],
    };
static mut l_Vector_set___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_set___auto__1___closed__8_value) as *mut leanh::LeanObject;
static mut l_Vector_set___auto__1___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_set___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_set___auto__1___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_set___auto__1___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_set___auto__1___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_set___auto__1___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_set___auto__1___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_set___auto__1___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_set___auto__1___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_set___auto__1___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_set___auto__1___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_set___auto__1___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_set___auto__1___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_set___auto__1___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_set___auto__1___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_set___auto__1___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_set___auto__1___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_set___auto__1___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Vector_set___auto__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Vector_foldl___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_foldl___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_foldl___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Vector_foldl___redArg___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_foldl___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_foldl___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Vector_foldl___redArg___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_foldl___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_foldl___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_Vector_foldl___redArg___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_foldl___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_foldl___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l_Vector_foldl___redArg___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_foldl___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_foldl___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l_Vector_foldl___redArg___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_foldl___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_foldl___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_Vector_foldl___redArg___closed__6_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_foldl___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_foldl___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l_Vector_foldl___redArg___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_foldl___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_foldl___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_foldl___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_foldl___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l_Vector_foldl___redArg___closed__8_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_foldl___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_foldl___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_foldl___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_foldl___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_foldl___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_foldl___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_foldl___redArg___closed__8_value) as *mut leanh::LeanObject;
pub static l_Vector_foldl___redArg___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_foldl___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_foldl___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_foldl___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_foldl___redArg___closed__9_value) as *mut leanh::LeanObject;
pub static l_Vector_mapM___redArg___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Vector_mapM___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_mapM___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Vector_flatten___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Vector_flatten___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_flatten___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_flatten___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Vector_flatten___redArg___closed__1_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Vector_flatten___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_flatten___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Vector_flatten___redArg___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Array_append___redArg___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_flatten___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_flatten___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Vector_swap___auto__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Vector_swap___auto__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Vector_swapAt___auto__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Vector_swapAt_x21___redArg___closed__0_value: leanh::LeanStringObject<22> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 65, 114, 114, 97, 121, 46, 66, 97, 115,
            105, 99, 0,
        ],
    };
static mut l_Vector_swapAt_x21___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_swapAt_x21___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Vector_swapAt_x21___redArg___closed__1_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [65, 114, 114, 97, 121, 46, 115, 119, 97, 112, 65, 116, 33, 0],
    };
static mut l_Vector_swapAt_x21___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_swapAt_x21___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Vector_swapAt_x21___redArg___closed__2_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [105, 110, 100, 101, 120, 32, 0],
    };
static mut l_Vector_swapAt_x21___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_swapAt_x21___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Vector_swapAt_x21___redArg___closed__3_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            32, 111, 117, 116, 32, 111, 102, 32, 98, 111, 117, 110, 100, 115, 0,
        ],
    };
static mut l_Vector_swapAt_x21___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_swapAt_x21___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Vector_eraseIdx___auto__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Vector_eraseIdx_x21___redArg___closed__0_value: leanh::LeanStringObject<23> =
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
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 86, 101, 99, 116, 111, 114, 46, 66, 97,
            115, 105, 99, 0,
        ],
    };
static mut l_Vector_eraseIdx_x21___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_eraseIdx_x21___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Vector_eraseIdx_x21___redArg___closed__1_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            86, 101, 99, 116, 111, 114, 46, 101, 114, 97, 115, 101, 73, 100, 120, 33, 0,
        ],
    };
static mut l_Vector_eraseIdx_x21___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_eraseIdx_x21___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Vector_eraseIdx_x21___redArg___closed__2_value: leanh::LeanStringObject<20> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            105, 110, 100, 101, 120, 32, 111, 117, 116, 32, 111, 102, 32, 98, 111, 117, 110, 100,
            115, 0,
        ],
    };
static mut l_Vector_eraseIdx_x21___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_eraseIdx_x21___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Vector_eraseIdx_x21___redArg___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_eraseIdx_x21___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Vector_insertIdx___auto__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Vector_insertIdx_x21___redArg___closed__0_value: leanh::LeanStringObject<18> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            86, 101, 99, 116, 111, 114, 46, 105, 110, 115, 101, 114, 116, 73, 100, 120, 33, 0,
        ],
    };
static mut l_Vector_insertIdx_x21___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_insertIdx_x21___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Vector_insertIdx_x21___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_insertIdx_x21___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Vector_findM_x3f___redArg___closed__0_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_findM_x3f___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_findM_x3f___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Vector_lex___auto__1___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [101, 120, 97, 99, 116, 0],
    };
static mut l_Vector_lex___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_lex___auto__1___closed__0_value) as *mut leanh::LeanObject;
static l_Vector_lex___auto__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Vector_lex___auto__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector_lex___auto__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Vector_lex___auto__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_lex___auto__1___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_set___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Vector_lex___auto__1___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_lex___auto__1___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_lex___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            14997215300048349804 as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_lex___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_lex___auto__1___closed__1_value) as *mut leanh::LeanObject;
static mut l_Vector_lex___auto__1___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Vector_lex___auto__1___closed__4_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [112, 97, 114, 101, 110, 0],
    };
static mut l_Vector_lex___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_lex___auto__1___closed__4_value) as *mut leanh::LeanObject;
static l_Vector_lex___auto__1___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Vector_lex___auto__1___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector_lex___auto__1___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Vector_lex___auto__1___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector_lex___auto__1___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Vector_lex___auto__1___closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_lex___auto__1___closed__5_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_lex___auto__1___closed__4_value)
                as *mut leanh::LeanObject,
            7932075773091973500 as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_lex___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_lex___auto__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Vector_lex___auto__1___closed__6_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0,
        ],
    };
static mut l_Vector_lex___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_lex___auto__1___closed__6_value) as *mut leanh::LeanObject;
static l_Vector_lex___auto__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Vector_lex___auto__1___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector_lex___auto__1___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Vector_lex___auto__1___closed__7_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector_lex___auto__1___closed__7_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Vector_lex___auto__1___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_lex___auto__1___closed__7_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_lex___auto__1___closed__6_value)
                as *mut leanh::LeanObject,
            7306243862518720553 as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_lex___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_lex___auto__1___closed__7_value) as *mut leanh::LeanObject;
static mut l_Vector_lex___auto__1___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Vector_lex___auto__1___closed__10_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0],
    };
static mut l_Vector_lex___auto__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_lex___auto__1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Vector_lex___auto__1___closed__11_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_lex___auto__1___closed__10_value)
                as *mut leanh::LeanObject,
            9871775667037945883 as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_lex___auto__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_lex___auto__1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Vector_lex___auto__1___closed__12_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [91, 97, 110, 111, 110, 121, 109, 111, 117, 115, 93, 0],
    };
static mut l_Vector_lex___auto__1___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_lex___auto__1___closed__12_value) as *mut leanh::LeanObject;
static mut l_Vector_lex___auto__1___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Vector_lex___auto__1___closed__21_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [116, 101, 114, 109, 95, 60, 95, 0],
    };
static mut l_Vector_lex___auto__1___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_lex___auto__1___closed__21_value) as *mut leanh::LeanObject;
pub static l_Vector_lex___auto__1___closed__22_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_lex___auto__1___closed__21_value)
                as *mut leanh::LeanObject,
            6883052497475924672 as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_lex___auto__1___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_lex___auto__1___closed__22_value) as *mut leanh::LeanObject;
pub static l_Vector_lex___auto__1___closed__23_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [99, 100, 111, 116, 0],
    };
static mut l_Vector_lex___auto__1___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_lex___auto__1___closed__23_value) as *mut leanh::LeanObject;
static l_Vector_lex___auto__1___closed__24_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Vector_lex___auto__1___closed__24_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector_lex___auto__1___closed__24_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Vector_lex___auto__1___closed__24_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Vector_lex___auto__1___closed__24_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Vector_lex___auto__1___closed__24_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_lex___auto__1___closed__24_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_lex___auto__1___closed__23_value)
                as *mut leanh::LeanObject,
            6167508377434939095 as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_lex___auto__1___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_lex___auto__1___closed__24_value) as *mut leanh::LeanObject;
pub static l_Vector_lex___auto__1___closed__25_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 1,
        m_data: [194, 183, 0],
    };
static mut l_Vector_lex___auto__1___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_lex___auto__1___closed__25_value) as *mut leanh::LeanObject;
static mut l_Vector_lex___auto__1___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__27_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__27: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__28_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__28: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__29_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__29: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__30_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__30: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Vector_lex___auto__1___closed__31_value: leanh::LeanStringObject<2> =
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
        m_data: [60, 0],
    };
static mut l_Vector_lex___auto__1___closed__31: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_lex___auto__1___closed__31_value) as *mut leanh::LeanObject;
static mut l_Vector_lex___auto__1___closed__32_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__32: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__33_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__33: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__34_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__34: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__35_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__35: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__36_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__36: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__37_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__37: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__38_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__38: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__39_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__39: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__40_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__40: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__41_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__41: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__42_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__42: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__43_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__43: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__44_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__44: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__45_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__45: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__46_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__46: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Vector_lex___auto__1___closed__47_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Vector_lex___auto__1___closed__47: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Vector_lex___auto__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Vector_lex___redArg___closed__0_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_lex___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_lex___redArg___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_instReprVector_repr___redArg___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3217_ = leanh::lean_unsigned_to_nat(11);
    v___x_3218_ = lean_nat_to_int(v___x_3217_);
    return v___x_3218_;
}
pub unsafe fn _init_l_instReprVector_repr___redArg___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3229_ = l_instReprVector_repr___redArg___closed__0;
    v___x_3230_ = lean_string_length(v___x_3229_);
    return v___x_3230_;
}
pub unsafe fn _init_l_instReprVector_repr___redArg___closed__16() -> *mut leanh::LeanObject {
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3231_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instReprVector_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(l_instReprVector_repr___redArg___closed__15_once),
        _init_l_instReprVector_repr___redArg___closed__15,
    );
    v___x_3232_ = lean_nat_to_int(v___x_3231_);
    return v___x_3232_;
}
pub unsafe fn l_instReprVector_repr___redArg(
    mut v_inst_3237_: *mut leanh::LeanObject,
    mut v_x_3238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: u8 = 0;
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3239_ = l_instReprVector_repr___redArg___closed__5;
    v___x_3240_ = l_instReprVector_repr___redArg___closed__6;
    v___x_3241_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instReprVector_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_instReprVector_repr___redArg___closed__7_once),
        _init_l_instReprVector_repr___redArg___closed__7,
    );
    v___x_3242_ = l_Array_repr___redArg(v_inst_3237_, v_x_3238_);
    v___x_3243_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3243_, 0, v___x_3241_);
    leanh::lean_ctor_set(v___x_3243_, 1, v___x_3242_);
    v___x_3244_ = 0;
    v___x_3245_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3245_, 0, v___x_3243_);
    leanh::lean_ctor_set_uint8(
        v___x_3245_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3244_,
    );
    v___x_3246_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3246_, 0, v___x_3240_);
    leanh::lean_ctor_set(v___x_3246_, 1, v___x_3245_);
    v___x_3247_ = l_instReprVector_repr___redArg___closed__9;
    v___x_3248_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3248_, 0, v___x_3246_);
    leanh::lean_ctor_set(v___x_3248_, 1, v___x_3247_);
    v___x_3249_ = leanh::lean_box(1);
    v___x_3250_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3250_, 0, v___x_3248_);
    leanh::lean_ctor_set(v___x_3250_, 1, v___x_3249_);
    v___x_3251_ = l_instReprVector_repr___redArg___closed__11;
    v___x_3252_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3252_, 0, v___x_3250_);
    leanh::lean_ctor_set(v___x_3252_, 1, v___x_3251_);
    v___x_3253_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3253_, 0, v___x_3252_);
    leanh::lean_ctor_set(v___x_3253_, 1, v___x_3239_);
    v___x_3254_ = l_instReprVector_repr___redArg___closed__13;
    v___x_3255_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3255_, 0, v___x_3253_);
    leanh::lean_ctor_set(v___x_3255_, 1, v___x_3254_);
    v___x_3256_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instReprVector_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_instReprVector_repr___redArg___closed__16_once),
        _init_l_instReprVector_repr___redArg___closed__16,
    );
    v___x_3257_ = l_instReprVector_repr___redArg___closed__17;
    v___x_3258_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3258_, 0, v___x_3257_);
    leanh::lean_ctor_set(v___x_3258_, 1, v___x_3255_);
    v___x_3259_ = l_instReprVector_repr___redArg___closed__18;
    v___x_3260_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3260_, 0, v___x_3258_);
    leanh::lean_ctor_set(v___x_3260_, 1, v___x_3259_);
    v___x_3261_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3261_, 0, v___x_3256_);
    leanh::lean_ctor_set(v___x_3261_, 1, v___x_3260_);
    v___x_3262_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3262_, 0, v___x_3261_);
    leanh::lean_ctor_set_uint8(
        v___x_3262_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3244_,
    );
    return v___x_3262_;
}
pub unsafe fn l_instReprVector_repr(
    mut v_00_u03b1_3263_: *mut leanh::LeanObject,
    mut v_n_3264_: *mut leanh::LeanObject,
    mut v_inst_3265_: *mut leanh::LeanObject,
    mut v_x_3266_: *mut leanh::LeanObject,
    mut v_prec_3267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3268_ = l_instReprVector_repr___redArg(v_inst_3265_, v_x_3266_);
    return v___x_3268_;
}
pub unsafe fn l_instReprVector_repr___boxed(
    mut v_00_u03b1_3269_: *mut leanh::LeanObject,
    mut v_n_3270_: *mut leanh::LeanObject,
    mut v_inst_3271_: *mut leanh::LeanObject,
    mut v_x_3272_: *mut leanh::LeanObject,
    mut v_prec_3273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3274_ = l_instReprVector_repr(
        v_00_u03b1_3269_,
        v_n_3270_,
        v_inst_3271_,
        v_x_3272_,
        v_prec_3273_,
    );
    leanh::lean_dec(v_prec_3273_);
    leanh::lean_dec(v_n_3270_);
    return v_res_3274_;
}
pub unsafe fn l_instReprVector___redArg(
    mut v_n_3275_: *mut leanh::LeanObject,
    mut v_inst_3276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3277_ = leanh::lean_alloc_closure(
        l_instReprVector_repr___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___x_3277_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3277_, 1, v_n_3275_);
    leanh::lean_closure_set(v___x_3277_, 2, v_inst_3276_);
    return v___x_3277_;
}
pub unsafe fn l_instReprVector(
    mut v_00_u03b1_3278_: *mut leanh::LeanObject,
    mut v_n_3279_: *mut leanh::LeanObject,
    mut v_inst_3280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3281_ = leanh::lean_alloc_closure(
        l_instReprVector_repr___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___x_3281_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3281_, 1, v_n_3279_);
    leanh::lean_closure_set(v___x_3281_, 2, v_inst_3280_);
    return v___x_3281_;
}
pub unsafe fn l_instDecidableEqVector_decEq___redArg(
    mut v_inst_3282_: *mut leanh::LeanObject,
    mut v_x_3283_: *mut leanh::LeanObject,
    mut v_x_3284_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3285_: u8 = 0;
    v___x_3285_ = l_Array_instDecidableEqImpl___redArg(v_inst_3282_, v_x_3283_, v_x_3284_);
    return v___x_3285_;
}
pub unsafe fn l_instDecidableEqVector_decEq___redArg___boxed(
    mut v_inst_3286_: *mut leanh::LeanObject,
    mut v_x_3287_: *mut leanh::LeanObject,
    mut v_x_3288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3289_: u8 = 0;
    let mut v_r_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3289_ = l_instDecidableEqVector_decEq___redArg(v_inst_3286_, v_x_3287_, v_x_3288_);
    leanh::lean_dec_ref(v_x_3288_);
    leanh::lean_dec_ref(v_x_3287_);
    v_r_3290_ = leanh::lean_box((v_res_3289_) as usize);
    return v_r_3290_;
}
pub unsafe fn l_instDecidableEqVector_decEq(
    mut v_00_u03b1_3291_: *mut leanh::LeanObject,
    mut v_n_3292_: *mut leanh::LeanObject,
    mut v_inst_3293_: *mut leanh::LeanObject,
    mut v_x_3294_: *mut leanh::LeanObject,
    mut v_x_3295_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3296_: u8 = 0;
    v___x_3296_ = l_Array_instDecidableEqImpl___redArg(v_inst_3293_, v_x_3294_, v_x_3295_);
    return v___x_3296_;
}
pub unsafe fn l_instDecidableEqVector_decEq___boxed(
    mut v_00_u03b1_3297_: *mut leanh::LeanObject,
    mut v_n_3298_: *mut leanh::LeanObject,
    mut v_inst_3299_: *mut leanh::LeanObject,
    mut v_x_3300_: *mut leanh::LeanObject,
    mut v_x_3301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3302_: u8 = 0;
    let mut v_r_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3302_ = l_instDecidableEqVector_decEq(
        v_00_u03b1_3297_,
        v_n_3298_,
        v_inst_3299_,
        v_x_3300_,
        v_x_3301_,
    );
    leanh::lean_dec_ref(v_x_3301_);
    leanh::lean_dec_ref(v_x_3300_);
    leanh::lean_dec(v_n_3298_);
    v_r_3303_ = leanh::lean_box((v_res_3302_) as usize);
    return v_r_3303_;
}
pub unsafe fn l_instDecidableEqVector___redArg(
    mut v_inst_3304_: *mut leanh::LeanObject,
    mut v_x_3305_: *mut leanh::LeanObject,
    mut v_x_3306_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3307_: u8 = 0;
    v___x_3307_ = l_Array_instDecidableEqImpl___redArg(v_inst_3304_, v_x_3305_, v_x_3306_);
    return v___x_3307_;
}
pub unsafe fn l_instDecidableEqVector___redArg___boxed(
    mut v_inst_3308_: *mut leanh::LeanObject,
    mut v_x_3309_: *mut leanh::LeanObject,
    mut v_x_3310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3311_: u8 = 0;
    let mut v_r_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3311_ = l_instDecidableEqVector___redArg(v_inst_3308_, v_x_3309_, v_x_3310_);
    leanh::lean_dec_ref(v_x_3310_);
    leanh::lean_dec_ref(v_x_3309_);
    v_r_3312_ = leanh::lean_box((v_res_3311_) as usize);
    return v_r_3312_;
}
pub unsafe fn l_instDecidableEqVector(
    mut v_00_u03b1_3313_: *mut leanh::LeanObject,
    mut v_n_3314_: *mut leanh::LeanObject,
    mut v_inst_3315_: *mut leanh::LeanObject,
    mut v_x_3316_: *mut leanh::LeanObject,
    mut v_x_3317_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3318_: u8 = 0;
    v___x_3318_ = l_Array_instDecidableEqImpl___redArg(v_inst_3315_, v_x_3316_, v_x_3317_);
    return v___x_3318_;
}
pub unsafe fn l_instDecidableEqVector___boxed(
    mut v_00_u03b1_3319_: *mut leanh::LeanObject,
    mut v_n_3320_: *mut leanh::LeanObject,
    mut v_inst_3321_: *mut leanh::LeanObject,
    mut v_x_3322_: *mut leanh::LeanObject,
    mut v_x_3323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3324_: u8 = 0;
    let mut v_r_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3324_ = l_instDecidableEqVector(
        v_00_u03b1_3319_,
        v_n_3320_,
        v_inst_3321_,
        v_x_3322_,
        v_x_3323_,
    );
    leanh::lean_dec_ref(v_x_3323_);
    leanh::lean_dec_ref(v_x_3322_);
    leanh::lean_dec(v_n_3320_);
    v_r_3325_ = leanh::lean_box((v_res_3324_) as usize);
    return v_r_3325_;
}
pub unsafe fn l_Array_toVector___redArg(
    mut v_xs_3326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_xs_3326_);
    return v_xs_3326_;
}
pub unsafe fn l_Array_toVector___redArg___boxed(
    mut v_xs_3327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3328_ = l_Array_toVector___redArg(v_xs_3327_);
    leanh::lean_dec_ref(v_xs_3327_);
    return v_res_3328_;
}
pub unsafe fn l_Array_toVector(
    mut v_00_u03b1_3329_: *mut leanh::LeanObject,
    mut v_xs_3330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_xs_3330_);
    return v_xs_3330_;
}
pub unsafe fn l_Array_toVector___boxed(
    mut v_00_u03b1_3331_: *mut leanh::LeanObject,
    mut v_xs_3332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3333_ = l_Array_toVector(v_00_u03b1_3331_, v_xs_3332_);
    leanh::lean_dec_ref(v_xs_3332_);
    return v_res_3333_;
}
pub unsafe fn l_Vector_size___redArg(
    mut v_n_3334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_n_3334_);
    return v_n_3334_;
}
pub unsafe fn l_Vector_size___redArg___boxed(
    mut v_n_3335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3336_ = l_Vector_size___redArg(v_n_3335_);
    leanh::lean_dec(v_n_3335_);
    return v_res_3336_;
}
pub unsafe fn l_Vector_size(
    mut v_00_u03b1_3337_: *mut leanh::LeanObject,
    mut v_n_3338_: *mut leanh::LeanObject,
    mut v_x_3339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_n_3338_);
    return v_n_3338_;
}
pub unsafe fn l_Vector_size___boxed(
    mut v_00_u03b1_3340_: *mut leanh::LeanObject,
    mut v_n_3341_: *mut leanh::LeanObject,
    mut v_x_3342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3343_ = l_Vector_size(v_00_u03b1_3340_, v_n_3341_, v_x_3342_);
    leanh::lean_dec_ref(v_x_3342_);
    leanh::lean_dec(v_n_3341_);
    return v_res_3343_;
}
pub unsafe fn _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3401_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__5;
    v___x_3402_ = l_String_toRawSubstring_x27(v___x_3401_);
    return v___x_3402_;
}
pub unsafe fn _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3429_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__18;
    v___x_3430_ = l_String_toRawSubstring_x27(v___x_3429_);
    return v___x_3430_;
}
pub unsafe fn _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3439_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_3439_;
}
pub unsafe fn _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3441_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__27;
    v___x_3442_ = l_String_toRawSubstring_x27(v___x_3441_);
    return v___x_3442_;
}
pub unsafe fn l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1(
    mut v_x_3451_: *mut leanh::LeanObject,
    mut v_a_3452_: *mut leanh::LeanObject,
    mut v_a_3453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: u8 = 0;
    v___x_3454_ = l_Vector_term_x23v_x5b___x2c_x5d___closed__2;
    leanh::lean_inc(v_x_3451_);
    v___x_3455_ = l_Lean_Syntax_isOfKind(v_x_3451_, v___x_3454_);
    if v___x_3455_ == 0 {
        let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_3451_);
        v___x_3456_ = leanh::lean_box(1);
        v___x_3457_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3457_, 0, v___x_3456_);
        leanh::lean_ctor_set(v___x_3457_, 1, v_a_3453_);
        return v___x_3457_;
    } else {
        let mut v_quotContext_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_elems_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3464_: u8 = 0;
        let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_3458_ = leanh::lean_ctor_get(v_a_3452_, 1);
        v_currMacroScope_3459_ = leanh::lean_ctor_get(v_a_3452_, 2);
        v_ref_3460_ = leanh::lean_ctor_get(v_a_3452_, 5);
        v___x_3461_ = leanh::lean_unsigned_to_nat(1);
        v___x_3462_ = l_Lean_Syntax_getArg(v_x_3451_, v___x_3461_);
        leanh::lean_dec(v_x_3451_);
        v_elems_3463_ = l_Lean_Syntax_getArgs(v___x_3462_);
        leanh::lean_dec(v___x_3462_);
        v___x_3464_ = 0;
        v___x_3465_ = l_Lean_SourceInfo_fromRef(v_ref_3460_, v___x_3464_);
        v___x_3466_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4;
        v___x_3467_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6), core::ptr::addr_of_mut!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6_once), _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6);
        v___x_3468_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8;
        leanh::lean_inc_n(v_currMacroScope_3459_, 3);
        leanh::lean_inc_n(v_quotContext_3458_, 3);
        v___x_3469_ =
            l_Lean_addMacroScope(v_quotContext_3458_, v___x_3468_, v_currMacroScope_3459_);
        v___x_3470_ = leanh::lean_box(0);
        v___x_3471_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__12;
        leanh::lean_inc_n(v___x_3465_, 12);
        v___x_3472_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_3472_, 0, v___x_3465_);
        leanh::lean_ctor_set(v___x_3472_, 1, v___x_3467_);
        leanh::lean_ctor_set(v___x_3472_, 2, v___x_3469_);
        leanh::lean_ctor_set(v___x_3472_, 3, v___x_3471_);
        v___x_3473_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14;
        v___x_3474_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16;
        v___x_3475_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17;
        v___x_3476_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3476_, 0, v___x_3465_);
        leanh::lean_ctor_set(v___x_3476_, 1, v___x_3475_);
        v___x_3477_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19), core::ptr::addr_of_mut!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19_once), _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19);
        v___x_3478_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__20;
        v___x_3479_ =
            l_Lean_addMacroScope(v_quotContext_3458_, v___x_3478_, v_currMacroScope_3459_);
        v___x_3480_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_3480_, 0, v___x_3465_);
        leanh::lean_ctor_set(v___x_3480_, 1, v___x_3477_);
        leanh::lean_ctor_set(v___x_3480_, 2, v___x_3479_);
        leanh::lean_ctor_set(v___x_3480_, 3, v___x_3470_);
        v___x_3481_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__21;
        v___x_3482_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3482_, 0, v___x_3465_);
        leanh::lean_ctor_set(v___x_3482_, 1, v___x_3481_);
        v___x_3483_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_elems_3463_);
        v___x_3484_ = lean_array_get_size(v___x_3483_);
        leanh::lean_dec_ref(v___x_3483_);
        v___x_3485_ = l_Nat_reprFast(v___x_3484_);
        v___x_3486_ = leanh::lean_box(2);
        v___x_3487_ = l_Lean_Syntax_mkNumLit(v___x_3485_, v___x_3486_);
        v___x_3488_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22;
        v___x_3489_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3489_, 0, v___x_3465_);
        leanh::lean_ctor_set(v___x_3489_, 1, v___x_3488_);
        v___x_3490_ = l_Lean_Syntax_node5(
            v___x_3465_,
            v___x_3474_,
            v___x_3476_,
            v___x_3480_,
            v___x_3482_,
            v___x_3487_,
            v___x_3489_,
        );
        v___x_3491_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24;
        v___x_3492_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__25;
        v___x_3493_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3493_, 0, v___x_3465_);
        leanh::lean_ctor_set(v___x_3493_, 1, v___x_3492_);
        v___x_3494_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26), core::ptr::addr_of_mut!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26_once), _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26);
        v___x_3495_ = l_Array_append___redArg(v___x_3494_, v_elems_3463_);
        leanh::lean_dec_ref(v_elems_3463_);
        v___x_3496_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_3496_, 0, v___x_3465_);
        leanh::lean_ctor_set(v___x_3496_, 1, v___x_3473_);
        leanh::lean_ctor_set(v___x_3496_, 2, v___x_3495_);
        v___x_3497_ = l_Vector_term_x23v_x5b___x2c_x5d___closed__17;
        v___x_3498_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3498_, 0, v___x_3465_);
        leanh::lean_ctor_set(v___x_3498_, 1, v___x_3497_);
        v___x_3499_ = l_Lean_Syntax_node3(
            v___x_3465_,
            v___x_3491_,
            v___x_3493_,
            v___x_3496_,
            v___x_3498_,
        );
        v___x_3500_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28), core::ptr::addr_of_mut!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28_once), _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28);
        v___x_3501_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__29;
        v___x_3502_ =
            l_Lean_addMacroScope(v_quotContext_3458_, v___x_3501_, v_currMacroScope_3459_);
        v___x_3503_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__31;
        v___x_3504_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_3504_, 0, v___x_3465_);
        leanh::lean_ctor_set(v___x_3504_, 1, v___x_3500_);
        leanh::lean_ctor_set(v___x_3504_, 2, v___x_3502_);
        leanh::lean_ctor_set(v___x_3504_, 3, v___x_3503_);
        v___x_3505_ = l_Lean_Syntax_node3(
            v___x_3465_,
            v___x_3473_,
            v___x_3490_,
            v___x_3499_,
            v___x_3504_,
        );
        v___x_3506_ = l_Lean_Syntax_node2(v___x_3465_, v___x_3466_, v___x_3472_, v___x_3505_);
        v___x_3507_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3507_, 0, v___x_3506_);
        leanh::lean_ctor_set(v___x_3507_, 1, v_a_3453_);
        return v___x_3507_;
    }
}
pub unsafe fn l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___boxed(
    mut v_x_3508_: *mut leanh::LeanObject,
    mut v_a_3509_: *mut leanh::LeanObject,
    mut v_a_3510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3511_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1(v_x_3508_, v_a_3509_, v_a_3510_);
    leanh::lean_dec_ref(v_a_3509_);
    return v_res_3511_;
}
pub unsafe fn l_Vector_unexpandMk(
    mut v_x_3512_: *mut leanh::LeanObject,
    mut v_a_3513_: *mut leanh::LeanObject,
    mut v_a_3514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: u8 = 0;
    v___x_3515_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4;
    leanh::lean_inc(v_x_3512_);
    v___x_3516_ = l_Lean_Syntax_isOfKind(v_x_3512_, v___x_3515_);
    if v___x_3516_ == 0 {
        let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_3512_);
        v___x_3517_ = leanh::lean_box(0);
        v___x_3518_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3518_, 0, v___x_3517_);
        leanh::lean_ctor_set(v___x_3518_, 1, v_a_3514_);
        return v___x_3518_;
    } else {
        let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3522_: u8 = 0;
        v___x_3519_ = leanh::lean_unsigned_to_nat(1);
        v___x_3520_ = l_Lean_Syntax_getArg(v_x_3512_, v___x_3519_);
        leanh::lean_dec(v_x_3512_);
        v___x_3521_ = leanh::lean_unsigned_to_nat(2);
        leanh::lean_inc(v___x_3520_);
        v___x_3522_ = l_Lean_Syntax_matchesNull(v___x_3520_, v___x_3521_);
        if v___x_3522_ == 0 {
            let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_3520_);
            v___x_3523_ = leanh::lean_box(0);
            v___x_3524_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_3524_, 0, v___x_3523_);
            leanh::lean_ctor_set(v___x_3524_, 1, v_a_3514_);
            return v___x_3524_;
        } else {
            let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3528_: u8 = 0;
            v___x_3525_ = leanh::lean_unsigned_to_nat(0);
            v___x_3526_ = l_Lean_Syntax_getArg(v___x_3520_, v___x_3525_);
            leanh::lean_dec(v___x_3520_);
            v___x_3527_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24;
            leanh::lean_inc(v___x_3526_);
            v___x_3528_ = l_Lean_Syntax_isOfKind(v___x_3526_, v___x_3527_);
            if v___x_3528_ == 0 {
                let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_3526_);
                v___x_3529_ = leanh::lean_box(0);
                v___x_3530_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3530_, 0, v___x_3529_);
                leanh::lean_ctor_set(v___x_3530_, 1, v_a_3514_);
                return v___x_3530_;
            } else {
                let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3533_: u8 = 0;
                let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3531_ = l_Lean_Syntax_getArg(v___x_3526_, v___x_3519_);
                leanh::lean_dec(v___x_3526_);
                v___x_3532_ = l_Lean_Syntax_getArgs(v___x_3531_);
                leanh::lean_dec(v___x_3531_);
                v___x_3533_ = 0;
                v___x_3534_ = l_Lean_SourceInfo_fromRef(v_a_3513_, v___x_3533_);
                v___x_3535_ = l_Vector_term_x23v_x5b___x2c_x5d___closed__2;
                v___x_3536_ = l_Vector_term_x23v_x5b___x2c_x5d___closed__5;
                leanh::lean_inc_n(v___x_3534_, 3);
                v___x_3537_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3537_, 0, v___x_3534_);
                leanh::lean_ctor_set(v___x_3537_, 1, v___x_3536_);
                v___x_3538_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14;
                v___x_3539_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26), core::ptr::addr_of_mut!(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26_once), _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26);
                v___x_3540_ = l_Array_append___redArg(v___x_3539_, v___x_3532_);
                leanh::lean_dec_ref(v___x_3532_);
                v___x_3541_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3541_, 0, v___x_3534_);
                leanh::lean_ctor_set(v___x_3541_, 1, v___x_3538_);
                leanh::lean_ctor_set(v___x_3541_, 2, v___x_3540_);
                v___x_3542_ = l_Vector_term_x23v_x5b___x2c_x5d___closed__17;
                v___x_3543_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3543_, 0, v___x_3534_);
                leanh::lean_ctor_set(v___x_3543_, 1, v___x_3542_);
                v___x_3544_ = l_Lean_Syntax_node3(
                    v___x_3534_,
                    v___x_3535_,
                    v___x_3537_,
                    v___x_3541_,
                    v___x_3543_,
                );
                v___x_3545_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3545_, 0, v___x_3544_);
                leanh::lean_ctor_set(v___x_3545_, 1, v_a_3514_);
                return v___x_3545_;
            }
        }
    }
}
pub unsafe fn l_Vector_unexpandMk___boxed(
    mut v_x_3546_: *mut leanh::LeanObject,
    mut v_a_3547_: *mut leanh::LeanObject,
    mut v_a_3548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3549_ = l_Vector_unexpandMk(v_x_3546_, v_a_3547_, v_a_3548_);
    leanh::lean_dec(v_a_3547_);
    return v_res_3549_;
}
pub unsafe fn l_Vector_toList___redArg(
    mut v_xs_3550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3551_ = lean_array_to_list(v_xs_3550_);
    return v___x_3551_;
}
pub unsafe fn l_Vector_toList(
    mut v_00_u03b1_3552_: *mut leanh::LeanObject,
    mut v_n_3553_: *mut leanh::LeanObject,
    mut v_xs_3554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3555_ = lean_array_to_list(v_xs_3554_);
    return v___x_3555_;
}
pub unsafe fn l_Vector_toList___boxed(
    mut v_00_u03b1_3556_: *mut leanh::LeanObject,
    mut v_n_3557_: *mut leanh::LeanObject,
    mut v_xs_3558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3559_ = l_Vector_toList(v_00_u03b1_3556_, v_n_3557_, v_xs_3558_);
    leanh::lean_dec(v_n_3557_);
    return v_res_3559_;
}
pub unsafe fn l_Vector_elimAsArray___redArg(
    mut v_mk_3560_: *mut leanh::LeanObject,
    mut v_x_3561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3562_ = leanh::lean_apply_2(v_mk_3560_, v_x_3561_, leanh::lean_box(0));
    return v___x_3562_;
}
pub unsafe fn l_Vector_elimAsArray(
    mut v_00_u03b1_3563_: *mut leanh::LeanObject,
    mut v_n_3564_: *mut leanh::LeanObject,
    mut v_motive_3565_: *mut leanh::LeanObject,
    mut v_mk_3566_: *mut leanh::LeanObject,
    mut v_x_3567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3568_ = leanh::lean_apply_2(v_mk_3566_, v_x_3567_, leanh::lean_box(0));
    return v___x_3568_;
}
pub unsafe fn l_Vector_elimAsArray___boxed(
    mut v_00_u03b1_3569_: *mut leanh::LeanObject,
    mut v_n_3570_: *mut leanh::LeanObject,
    mut v_motive_3571_: *mut leanh::LeanObject,
    mut v_mk_3572_: *mut leanh::LeanObject,
    mut v_x_3573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3574_ = l_Vector_elimAsArray(
        v_00_u03b1_3569_,
        v_n_3570_,
        v_motive_3571_,
        v_mk_3572_,
        v_x_3573_,
    );
    leanh::lean_dec(v_n_3570_);
    return v_res_3574_;
}
pub unsafe fn l_Vector_elimAsList___redArg(
    mut v_mk_3575_: *mut leanh::LeanObject,
    mut v_x_3576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toList_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toList_3577_ = lean_array_to_list(v_x_3576_);
    v___x_3578_ = leanh::lean_apply_2(v_mk_3575_, v_toList_3577_, leanh::lean_box(0));
    return v___x_3578_;
}
pub unsafe fn l_Vector_elimAsList(
    mut v_00_u03b1_3579_: *mut leanh::LeanObject,
    mut v_n_3580_: *mut leanh::LeanObject,
    mut v_motive_3581_: *mut leanh::LeanObject,
    mut v_mk_3582_: *mut leanh::LeanObject,
    mut v_x_3583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3584_ = l_Vector_elimAsList___redArg(v_mk_3582_, v_x_3583_);
    return v___x_3584_;
}
pub unsafe fn l_Vector_elimAsList___boxed(
    mut v_00_u03b1_3585_: *mut leanh::LeanObject,
    mut v_n_3586_: *mut leanh::LeanObject,
    mut v_motive_3587_: *mut leanh::LeanObject,
    mut v_mk_3588_: *mut leanh::LeanObject,
    mut v_x_3589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3590_ = l_Vector_elimAsList(
        v_00_u03b1_3585_,
        v_n_3586_,
        v_motive_3587_,
        v_mk_3588_,
        v_x_3589_,
    );
    leanh::lean_dec(v_n_3586_);
    return v_res_3590_;
}
pub unsafe fn l_Vector_emptyWithCapacity___redArg(
    mut v_capacity_3591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3592_ = lean_mk_empty_array_with_capacity(v_capacity_3591_);
    return v___x_3592_;
}
pub unsafe fn l_Vector_emptyWithCapacity___redArg___boxed(
    mut v_capacity_3593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3594_ = l_Vector_emptyWithCapacity___redArg(v_capacity_3593_);
    leanh::lean_dec(v_capacity_3593_);
    return v_res_3594_;
}
pub unsafe fn l_Vector_emptyWithCapacity(
    mut v_00_u03b1_3595_: *mut leanh::LeanObject,
    mut v_capacity_3596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3597_ = lean_mk_empty_array_with_capacity(v_capacity_3596_);
    return v___x_3597_;
}
pub unsafe fn l_Vector_emptyWithCapacity___boxed(
    mut v_00_u03b1_3598_: *mut leanh::LeanObject,
    mut v_capacity_3599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3600_ = l_Vector_emptyWithCapacity(v_00_u03b1_3598_, v_capacity_3599_);
    leanh::lean_dec(v_capacity_3599_);
    return v_res_3600_;
}
pub unsafe fn l_Vector_replicate___redArg(
    mut v_n_3601_: *mut leanh::LeanObject,
    mut v_v_3602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3603_ = lean_mk_array(v_n_3601_, v_v_3602_);
    return v___x_3603_;
}
pub unsafe fn l_Vector_replicate(
    mut v_00_u03b1_3604_: *mut leanh::LeanObject,
    mut v_n_3605_: *mut leanh::LeanObject,
    mut v_v_3606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3607_ = lean_mk_array(v_n_3605_, v_v_3606_);
    return v___x_3607_;
}
pub unsafe fn l_Vector_singleton___redArg(
    mut v_v_3608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3609_ = leanh::lean_unsigned_to_nat(1);
    v___x_3610_ = lean_mk_empty_array_with_capacity(v___x_3609_);
    v___x_3611_ = lean_array_push(v___x_3610_, v_v_3608_);
    return v___x_3611_;
}
pub unsafe fn l_Vector_singleton(
    mut v_00_u03b1_3612_: *mut leanh::LeanObject,
    mut v_v_3613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3614_ = leanh::lean_unsigned_to_nat(1);
    v___x_3615_ = lean_mk_empty_array_with_capacity(v___x_3614_);
    v___x_3616_ = lean_array_push(v___x_3615_, v_v_3613_);
    return v___x_3616_;
}
pub unsafe fn l_Vector_instInhabited___redArg(
    mut v_n_3617_: *mut leanh::LeanObject,
    mut v_inst_3618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3619_ = lean_mk_array(v_n_3617_, v_inst_3618_);
    return v___x_3619_;
}
pub unsafe fn l_Vector_instInhabited(
    mut v_00_u03b1_3620_: *mut leanh::LeanObject,
    mut v_n_3621_: *mut leanh::LeanObject,
    mut v_inst_3622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3623_ = lean_mk_array(v_n_3621_, v_inst_3622_);
    return v___x_3623_;
}
pub unsafe fn l_Vector_get___redArg(
    mut v_xs_3624_: *mut leanh::LeanObject,
    mut v_i_3625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3626_ = lean_array_fget_borrowed(v_xs_3624_, v_i_3625_);
    leanh::lean_inc(v___x_3626_);
    return v___x_3626_;
}
pub unsafe fn l_Vector_get___redArg___boxed(
    mut v_xs_3627_: *mut leanh::LeanObject,
    mut v_i_3628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3629_ = l_Vector_get___redArg(v_xs_3627_, v_i_3628_);
    leanh::lean_dec(v_i_3628_);
    leanh::lean_dec_ref(v_xs_3627_);
    return v_res_3629_;
}
pub unsafe fn l_Vector_get(
    mut v_00_u03b1_3630_: *mut leanh::LeanObject,
    mut v_n_3631_: *mut leanh::LeanObject,
    mut v_xs_3632_: *mut leanh::LeanObject,
    mut v_i_3633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3634_ = lean_array_fget_borrowed(v_xs_3632_, v_i_3633_);
    leanh::lean_inc(v___x_3634_);
    return v___x_3634_;
}
pub unsafe fn l_Vector_get___boxed(
    mut v_00_u03b1_3635_: *mut leanh::LeanObject,
    mut v_n_3636_: *mut leanh::LeanObject,
    mut v_xs_3637_: *mut leanh::LeanObject,
    mut v_i_3638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3639_ = l_Vector_get(v_00_u03b1_3635_, v_n_3636_, v_xs_3637_, v_i_3638_);
    leanh::lean_dec(v_i_3638_);
    leanh::lean_dec_ref(v_xs_3637_);
    leanh::lean_dec(v_n_3636_);
    return v_res_3639_;
}
pub unsafe fn l_Vector_uget___redArg(
    mut v_xs_3640_: *mut leanh::LeanObject,
    mut v_i_3641_: usize,
) -> *mut leanh::LeanObject {
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3642_ = lean_array_uget_borrowed(v_xs_3640_, v_i_3641_);
    leanh::lean_inc(v___x_3642_);
    return v___x_3642_;
}
pub unsafe fn l_Vector_uget___redArg___boxed(
    mut v_xs_3643_: *mut leanh::LeanObject,
    mut v_i_3644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3645_: usize = 0;
    let mut v_res_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3645_ = leanh::lean_unbox_usize(v_i_3644_);
    leanh::lean_dec(v_i_3644_);
    v_res_3646_ = l_Vector_uget___redArg(v_xs_3643_, v_i_boxed_3645_);
    leanh::lean_dec_ref(v_xs_3643_);
    return v_res_3646_;
}
pub unsafe fn l_Vector_uget(
    mut v_00_u03b1_3647_: *mut leanh::LeanObject,
    mut v_n_3648_: *mut leanh::LeanObject,
    mut v_xs_3649_: *mut leanh::LeanObject,
    mut v_i_3650_: usize,
    mut v_h_3651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3652_ = lean_array_uget_borrowed(v_xs_3649_, v_i_3650_);
    leanh::lean_inc(v___x_3652_);
    return v___x_3652_;
}
pub unsafe fn l_Vector_uget___boxed(
    mut v_00_u03b1_3653_: *mut leanh::LeanObject,
    mut v_n_3654_: *mut leanh::LeanObject,
    mut v_xs_3655_: *mut leanh::LeanObject,
    mut v_i_3656_: *mut leanh::LeanObject,
    mut v_h_3657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3658_: usize = 0;
    let mut v_res_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3658_ = leanh::lean_unbox_usize(v_i_3656_);
    leanh::lean_dec(v_i_3656_);
    v_res_3659_ = l_Vector_uget(
        v_00_u03b1_3653_,
        v_n_3654_,
        v_xs_3655_,
        v_i_boxed_3658_,
        v_h_3657_,
    );
    leanh::lean_dec_ref(v_xs_3655_);
    leanh::lean_dec(v_n_3654_);
    return v_res_3659_;
}
pub unsafe fn l_Vector_instGetElemNatLt___lam__0(
    mut v_xs_3660_: *mut leanh::LeanObject,
    mut v_i_3661_: *mut leanh::LeanObject,
    mut v_h_3662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3663_ = lean_array_fget_borrowed(v_xs_3660_, v_i_3661_);
    leanh::lean_inc(v___x_3663_);
    return v___x_3663_;
}
pub unsafe fn l_Vector_instGetElemNatLt___lam__0___boxed(
    mut v_xs_3664_: *mut leanh::LeanObject,
    mut v_i_3665_: *mut leanh::LeanObject,
    mut v_h_3666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3667_ = l_Vector_instGetElemNatLt___lam__0(v_xs_3664_, v_i_3665_, v_h_3666_);
    leanh::lean_dec(v_i_3665_);
    leanh::lean_dec_ref(v_xs_3664_);
    return v_res_3667_;
}
pub unsafe fn l_Vector_instGetElemNatLt(
    mut v_00_u03b1_3669_: *mut leanh::LeanObject,
    mut v_n_3670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3671_ = l_Vector_instGetElemNatLt___closed__0;
    return v___f_3671_;
}
pub unsafe fn l_Vector_instGetElemNatLt___boxed(
    mut v_00_u03b1_3672_: *mut leanh::LeanObject,
    mut v_n_3673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3674_ = l_Vector_instGetElemNatLt(v_00_u03b1_3672_, v_n_3673_);
    leanh::lean_dec(v_n_3673_);
    return v_res_3674_;
}
pub unsafe fn l_Vector_contains___redArg(
    mut v_inst_3675_: *mut leanh::LeanObject,
    mut v_xs_3676_: *mut leanh::LeanObject,
    mut v_a_3677_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3678_: u8 = 0;
    v___x_3678_ = l_Array_contains___redArg(v_inst_3675_, v_xs_3676_, v_a_3677_);
    return v___x_3678_;
}
pub unsafe fn l_Vector_contains___redArg___boxed(
    mut v_inst_3679_: *mut leanh::LeanObject,
    mut v_xs_3680_: *mut leanh::LeanObject,
    mut v_a_3681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3682_: u8 = 0;
    let mut v_r_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3682_ = l_Vector_contains___redArg(v_inst_3679_, v_xs_3680_, v_a_3681_);
    v_r_3683_ = leanh::lean_box((v_res_3682_) as usize);
    return v_r_3683_;
}
pub unsafe fn l_Vector_contains(
    mut v_00_u03b1_3684_: *mut leanh::LeanObject,
    mut v_n_3685_: *mut leanh::LeanObject,
    mut v_inst_3686_: *mut leanh::LeanObject,
    mut v_xs_3687_: *mut leanh::LeanObject,
    mut v_a_3688_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3689_: u8 = 0;
    v___x_3689_ = l_Array_contains___redArg(v_inst_3686_, v_xs_3687_, v_a_3688_);
    return v___x_3689_;
}
pub unsafe fn l_Vector_contains___boxed(
    mut v_00_u03b1_3690_: *mut leanh::LeanObject,
    mut v_n_3691_: *mut leanh::LeanObject,
    mut v_inst_3692_: *mut leanh::LeanObject,
    mut v_xs_3693_: *mut leanh::LeanObject,
    mut v_a_3694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3695_: u8 = 0;
    let mut v_r_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3695_ = l_Vector_contains(
        v_00_u03b1_3690_,
        v_n_3691_,
        v_inst_3692_,
        v_xs_3693_,
        v_a_3694_,
    );
    leanh::lean_dec(v_n_3691_);
    v_r_3696_ = leanh::lean_box((v_res_3695_) as usize);
    return v_r_3696_;
}
pub unsafe fn l_Vector_instMembership(
    mut v_00_u03b1_3697_: *mut leanh::LeanObject,
    mut v_n_3698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3699_ = leanh::lean_box(0);
    return v___x_3699_;
}
pub unsafe fn l_Vector_instMembership___boxed(
    mut v_00_u03b1_3700_: *mut leanh::LeanObject,
    mut v_n_3701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3702_ = l_Vector_instMembership(v_00_u03b1_3700_, v_n_3701_);
    leanh::lean_dec(v_n_3701_);
    return v_res_3702_;
}
pub unsafe fn l_Vector_getD___redArg(
    mut v_xs_3703_: *mut leanh::LeanObject,
    mut v_i_3704_: *mut leanh::LeanObject,
    mut v_default_3705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: u8 = 0;
    v___x_3706_ = lean_array_get_size(v_xs_3703_);
    v___x_3707_ = lean_nat_dec_lt(v_i_3704_, v___x_3706_);
    if v___x_3707_ == 0 {
        leanh::lean_inc(v_default_3705_);
        return v_default_3705_;
    } else {
        let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3708_ = lean_array_fget_borrowed(v_xs_3703_, v_i_3704_);
        leanh::lean_inc(v___x_3708_);
        return v___x_3708_;
    }
}
pub unsafe fn l_Vector_getD___redArg___boxed(
    mut v_xs_3709_: *mut leanh::LeanObject,
    mut v_i_3710_: *mut leanh::LeanObject,
    mut v_default_3711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3712_ = l_Vector_getD___redArg(v_xs_3709_, v_i_3710_, v_default_3711_);
    leanh::lean_dec(v_default_3711_);
    leanh::lean_dec(v_i_3710_);
    leanh::lean_dec_ref(v_xs_3709_);
    return v_res_3712_;
}
pub unsafe fn l_Vector_getD(
    mut v_00_u03b1_3713_: *mut leanh::LeanObject,
    mut v_n_3714_: *mut leanh::LeanObject,
    mut v_xs_3715_: *mut leanh::LeanObject,
    mut v_i_3716_: *mut leanh::LeanObject,
    mut v_default_3717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: u8 = 0;
    v___x_3718_ = lean_array_get_size(v_xs_3715_);
    v___x_3719_ = lean_nat_dec_lt(v_i_3716_, v___x_3718_);
    if v___x_3719_ == 0 {
        leanh::lean_inc(v_default_3717_);
        return v_default_3717_;
    } else {
        let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3720_ = lean_array_fget_borrowed(v_xs_3715_, v_i_3716_);
        leanh::lean_inc(v___x_3720_);
        return v___x_3720_;
    }
}
pub unsafe fn l_Vector_getD___boxed(
    mut v_00_u03b1_3721_: *mut leanh::LeanObject,
    mut v_n_3722_: *mut leanh::LeanObject,
    mut v_xs_3723_: *mut leanh::LeanObject,
    mut v_i_3724_: *mut leanh::LeanObject,
    mut v_default_3725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3726_ = l_Vector_getD(
        v_00_u03b1_3721_,
        v_n_3722_,
        v_xs_3723_,
        v_i_3724_,
        v_default_3725_,
    );
    leanh::lean_dec(v_default_3725_);
    leanh::lean_dec(v_i_3724_);
    leanh::lean_dec_ref(v_xs_3723_);
    leanh::lean_dec(v_n_3722_);
    return v_res_3726_;
}
pub unsafe fn l_Vector_back_x21___redArg(
    mut v_inst_3727_: *mut leanh::LeanObject,
    mut v_xs_3728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3729_ = lean_array_get_size(v_xs_3728_);
    v___x_3730_ = leanh::lean_unsigned_to_nat(1);
    v___x_3731_ = lean_nat_sub(v___x_3729_, v___x_3730_);
    v___x_3732_ = lean_array_get_borrowed(v_inst_3727_, v_xs_3728_, v___x_3731_);
    leanh::lean_dec(v___x_3731_);
    leanh::lean_inc(v___x_3732_);
    return v___x_3732_;
}
pub unsafe fn l_Vector_back_x21___redArg___boxed(
    mut v_inst_3733_: *mut leanh::LeanObject,
    mut v_xs_3734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3735_ = l_Vector_back_x21___redArg(v_inst_3733_, v_xs_3734_);
    leanh::lean_dec_ref(v_xs_3734_);
    leanh::lean_dec(v_inst_3733_);
    return v_res_3735_;
}
pub unsafe fn l_Vector_back_x21(
    mut v_00_u03b1_3736_: *mut leanh::LeanObject,
    mut v_n_3737_: *mut leanh::LeanObject,
    mut v_inst_3738_: *mut leanh::LeanObject,
    mut v_xs_3739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3740_ = lean_array_get_size(v_xs_3739_);
    v___x_3741_ = leanh::lean_unsigned_to_nat(1);
    v___x_3742_ = lean_nat_sub(v___x_3740_, v___x_3741_);
    v___x_3743_ = lean_array_get_borrowed(v_inst_3738_, v_xs_3739_, v___x_3742_);
    leanh::lean_dec(v___x_3742_);
    leanh::lean_inc(v___x_3743_);
    return v___x_3743_;
}
pub unsafe fn l_Vector_back_x21___boxed(
    mut v_00_u03b1_3744_: *mut leanh::LeanObject,
    mut v_n_3745_: *mut leanh::LeanObject,
    mut v_inst_3746_: *mut leanh::LeanObject,
    mut v_xs_3747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3748_ = l_Vector_back_x21(v_00_u03b1_3744_, v_n_3745_, v_inst_3746_, v_xs_3747_);
    leanh::lean_dec_ref(v_xs_3747_);
    leanh::lean_dec(v_inst_3746_);
    leanh::lean_dec(v_n_3745_);
    return v_res_3748_;
}
pub unsafe fn l_Vector_back_x3f___redArg(
    mut v_xs_3749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: u8 = 0;
    v___x_3750_ = lean_array_get_size(v_xs_3749_);
    v___x_3751_ = leanh::lean_unsigned_to_nat(1);
    v___x_3752_ = lean_nat_sub(v___x_3750_, v___x_3751_);
    v___x_3753_ = lean_nat_dec_lt(v___x_3752_, v___x_3750_);
    if v___x_3753_ == 0 {
        let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_3752_);
        v___x_3754_ = leanh::lean_box(0);
        return v___x_3754_;
    } else {
        let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3755_ = lean_array_fget_borrowed(v_xs_3749_, v___x_3752_);
        leanh::lean_dec(v___x_3752_);
        leanh::lean_inc(v___x_3755_);
        v___x_3756_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3756_, 0, v___x_3755_);
        return v___x_3756_;
    }
}
pub unsafe fn l_Vector_back_x3f___redArg___boxed(
    mut v_xs_3757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3758_ = l_Vector_back_x3f___redArg(v_xs_3757_);
    leanh::lean_dec_ref(v_xs_3757_);
    return v_res_3758_;
}
pub unsafe fn l_Vector_back_x3f(
    mut v_00_u03b1_3759_: *mut leanh::LeanObject,
    mut v_n_3760_: *mut leanh::LeanObject,
    mut v_xs_3761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: u8 = 0;
    v___x_3762_ = lean_array_get_size(v_xs_3761_);
    v___x_3763_ = leanh::lean_unsigned_to_nat(1);
    v___x_3764_ = lean_nat_sub(v___x_3762_, v___x_3763_);
    v___x_3765_ = lean_nat_dec_lt(v___x_3764_, v___x_3762_);
    if v___x_3765_ == 0 {
        let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_3764_);
        v___x_3766_ = leanh::lean_box(0);
        return v___x_3766_;
    } else {
        let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3767_ = lean_array_fget_borrowed(v_xs_3761_, v___x_3764_);
        leanh::lean_dec(v___x_3764_);
        leanh::lean_inc(v___x_3767_);
        v___x_3768_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3768_, 0, v___x_3767_);
        return v___x_3768_;
    }
}
pub unsafe fn l_Vector_back_x3f___boxed(
    mut v_00_u03b1_3769_: *mut leanh::LeanObject,
    mut v_n_3770_: *mut leanh::LeanObject,
    mut v_xs_3771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3772_ = l_Vector_back_x3f(v_00_u03b1_3769_, v_n_3770_, v_xs_3771_);
    leanh::lean_dec_ref(v_xs_3771_);
    leanh::lean_dec(v_n_3770_);
    return v_res_3772_;
}
pub unsafe fn l_Vector_back___redArg(
    mut v_n_3773_: *mut leanh::LeanObject,
    mut v_xs_3774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3775_ = leanh::lean_unsigned_to_nat(1);
    v___x_3776_ = lean_nat_sub(v_n_3773_, v___x_3775_);
    v___x_3777_ = lean_array_fget_borrowed(v_xs_3774_, v___x_3776_);
    leanh::lean_dec(v___x_3776_);
    leanh::lean_inc(v___x_3777_);
    return v___x_3777_;
}
pub unsafe fn l_Vector_back___redArg___boxed(
    mut v_n_3778_: *mut leanh::LeanObject,
    mut v_xs_3779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3780_ = l_Vector_back___redArg(v_n_3778_, v_xs_3779_);
    leanh::lean_dec_ref(v_xs_3779_);
    leanh::lean_dec(v_n_3778_);
    return v_res_3780_;
}
pub unsafe fn l_Vector_back(
    mut v_n_3781_: *mut leanh::LeanObject,
    mut v_00_u03b1_3782_: *mut leanh::LeanObject,
    mut v_inst_3783_: *mut leanh::LeanObject,
    mut v_xs_3784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3785_ = leanh::lean_unsigned_to_nat(1);
    v___x_3786_ = lean_nat_sub(v_n_3781_, v___x_3785_);
    v___x_3787_ = lean_array_fget_borrowed(v_xs_3784_, v___x_3786_);
    leanh::lean_dec(v___x_3786_);
    leanh::lean_inc(v___x_3787_);
    return v___x_3787_;
}
pub unsafe fn l_Vector_back___boxed(
    mut v_n_3788_: *mut leanh::LeanObject,
    mut v_00_u03b1_3789_: *mut leanh::LeanObject,
    mut v_inst_3790_: *mut leanh::LeanObject,
    mut v_xs_3791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3792_ = l_Vector_back(v_n_3788_, v_00_u03b1_3789_, v_inst_3790_, v_xs_3791_);
    leanh::lean_dec_ref(v_xs_3791_);
    leanh::lean_dec(v_n_3788_);
    return v_res_3792_;
}
pub unsafe fn l_Vector_head___redArg(
    mut v_xs_3793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3794_ = leanh::lean_unsigned_to_nat(0);
    v___x_3795_ = lean_array_fget_borrowed(v_xs_3793_, v___x_3794_);
    leanh::lean_inc(v___x_3795_);
    return v___x_3795_;
}
pub unsafe fn l_Vector_head___redArg___boxed(
    mut v_xs_3796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3797_ = l_Vector_head___redArg(v_xs_3796_);
    leanh::lean_dec_ref(v_xs_3796_);
    return v_res_3797_;
}
pub unsafe fn l_Vector_head(
    mut v_n_3798_: *mut leanh::LeanObject,
    mut v_00_u03b1_3799_: *mut leanh::LeanObject,
    mut v_inst_3800_: *mut leanh::LeanObject,
    mut v_xs_3801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3802_ = leanh::lean_unsigned_to_nat(0);
    v___x_3803_ = lean_array_fget_borrowed(v_xs_3801_, v___x_3802_);
    leanh::lean_inc(v___x_3803_);
    return v___x_3803_;
}
pub unsafe fn l_Vector_head___boxed(
    mut v_n_3804_: *mut leanh::LeanObject,
    mut v_00_u03b1_3805_: *mut leanh::LeanObject,
    mut v_inst_3806_: *mut leanh::LeanObject,
    mut v_xs_3807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3808_ = l_Vector_head(v_n_3804_, v_00_u03b1_3805_, v_inst_3806_, v_xs_3807_);
    leanh::lean_dec_ref(v_xs_3807_);
    leanh::lean_dec(v_n_3804_);
    return v_res_3808_;
}
pub unsafe fn l_Vector_push___redArg(
    mut v_xs_3809_: *mut leanh::LeanObject,
    mut v_x_3810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3811_ = lean_array_push(v_xs_3809_, v_x_3810_);
    return v___x_3811_;
}
pub unsafe fn l_Vector_push(
    mut v_00_u03b1_3812_: *mut leanh::LeanObject,
    mut v_n_3813_: *mut leanh::LeanObject,
    mut v_xs_3814_: *mut leanh::LeanObject,
    mut v_x_3815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3816_ = lean_array_push(v_xs_3814_, v_x_3815_);
    return v___x_3816_;
}
pub unsafe fn l_Vector_push___boxed(
    mut v_00_u03b1_3817_: *mut leanh::LeanObject,
    mut v_n_3818_: *mut leanh::LeanObject,
    mut v_xs_3819_: *mut leanh::LeanObject,
    mut v_x_3820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3821_ = l_Vector_push(v_00_u03b1_3817_, v_n_3818_, v_xs_3819_, v_x_3820_);
    leanh::lean_dec(v_n_3818_);
    return v_res_3821_;
}
pub unsafe fn l_Vector_pop___redArg(
    mut v_xs_3822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3823_ = lean_array_pop(v_xs_3822_);
    return v___x_3823_;
}
pub unsafe fn l_Vector_pop(
    mut v_00_u03b1_3824_: *mut leanh::LeanObject,
    mut v_n_3825_: *mut leanh::LeanObject,
    mut v_xs_3826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3827_ = lean_array_pop(v_xs_3826_);
    return v___x_3827_;
}
pub unsafe fn l_Vector_pop___boxed(
    mut v_00_u03b1_3828_: *mut leanh::LeanObject,
    mut v_n_3829_: *mut leanh::LeanObject,
    mut v_xs_3830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3831_ = l_Vector_pop(v_00_u03b1_3828_, v_n_3829_, v_xs_3830_);
    leanh::lean_dec(v_n_3829_);
    return v_res_3831_;
}
pub unsafe fn _init_l_Vector_set___auto__1___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3851_ = l_Vector_set___auto__1___closed__8;
    v___x_3852_ = l_Lean_mkAtom(v___x_3851_);
    return v___x_3852_;
}
pub unsafe fn _init_l_Vector_set___auto__1___closed__10() -> *mut leanh::LeanObject {
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3853_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__9),
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__9_once),
        _init_l_Vector_set___auto__1___closed__9,
    );
    v___x_3854_ = l_Vector_set___auto__1___closed__3;
    v___x_3855_ = lean_array_push(v___x_3854_, v___x_3853_);
    return v___x_3855_;
}
pub unsafe fn _init_l_Vector_set___auto__1___closed__11() -> *mut leanh::LeanObject {
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3856_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__10),
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__10_once),
        _init_l_Vector_set___auto__1___closed__10,
    );
    v___x_3857_ = l_Vector_set___auto__1___closed__7;
    v___x_3858_ = leanh::lean_box(2);
    v___x_3859_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3859_, 0, v___x_3858_);
    leanh::lean_ctor_set(v___x_3859_, 1, v___x_3857_);
    leanh::lean_ctor_set(v___x_3859_, 2, v___x_3856_);
    return v___x_3859_;
}
pub unsafe fn _init_l_Vector_set___auto__1___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3860_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__11),
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__11_once),
        _init_l_Vector_set___auto__1___closed__11,
    );
    v___x_3861_ = l_Vector_set___auto__1___closed__3;
    v___x_3862_ = lean_array_push(v___x_3861_, v___x_3860_);
    return v___x_3862_;
}
pub unsafe fn _init_l_Vector_set___auto__1___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3863_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__12_once),
        _init_l_Vector_set___auto__1___closed__12,
    );
    v___x_3864_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14;
    v___x_3865_ = leanh::lean_box(2);
    v___x_3866_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3866_, 0, v___x_3865_);
    leanh::lean_ctor_set(v___x_3866_, 1, v___x_3864_);
    leanh::lean_ctor_set(v___x_3866_, 2, v___x_3863_);
    return v___x_3866_;
}
pub unsafe fn _init_l_Vector_set___auto__1___closed__14() -> *mut leanh::LeanObject {
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3867_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__13_once),
        _init_l_Vector_set___auto__1___closed__13,
    );
    v___x_3868_ = l_Vector_set___auto__1___closed__3;
    v___x_3869_ = lean_array_push(v___x_3868_, v___x_3867_);
    return v___x_3869_;
}
pub unsafe fn _init_l_Vector_set___auto__1___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3870_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__14),
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__14_once),
        _init_l_Vector_set___auto__1___closed__14,
    );
    v___x_3871_ = l_Vector_set___auto__1___closed__5;
    v___x_3872_ = leanh::lean_box(2);
    v___x_3873_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3873_, 0, v___x_3872_);
    leanh::lean_ctor_set(v___x_3873_, 1, v___x_3871_);
    leanh::lean_ctor_set(v___x_3873_, 2, v___x_3870_);
    return v___x_3873_;
}
pub unsafe fn _init_l_Vector_set___auto__1___closed__16() -> *mut leanh::LeanObject {
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3874_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__15_once),
        _init_l_Vector_set___auto__1___closed__15,
    );
    v___x_3875_ = l_Vector_set___auto__1___closed__3;
    v___x_3876_ = lean_array_push(v___x_3875_, v___x_3874_);
    return v___x_3876_;
}
pub unsafe fn _init_l_Vector_set___auto__1___closed__17() -> *mut leanh::LeanObject {
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3877_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__16_once),
        _init_l_Vector_set___auto__1___closed__16,
    );
    v___x_3878_ = l_Vector_set___auto__1___closed__2;
    v___x_3879_ = leanh::lean_box(2);
    v___x_3880_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3880_, 0, v___x_3879_);
    leanh::lean_ctor_set(v___x_3880_, 1, v___x_3878_);
    leanh::lean_ctor_set(v___x_3880_, 2, v___x_3877_);
    return v___x_3880_;
}
pub unsafe fn _init_l_Vector_set___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3881_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__17_once),
        _init_l_Vector_set___auto__1___closed__17,
    );
    return v___x_3881_;
}
pub unsafe fn l_Vector_set___redArg(
    mut v_xs_3882_: *mut leanh::LeanObject,
    mut v_i_3883_: *mut leanh::LeanObject,
    mut v_x_3884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3885_ = lean_array_fset(v_xs_3882_, v_i_3883_, v_x_3884_);
    return v___x_3885_;
}
pub unsafe fn l_Vector_set___redArg___boxed(
    mut v_xs_3886_: *mut leanh::LeanObject,
    mut v_i_3887_: *mut leanh::LeanObject,
    mut v_x_3888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3889_ = l_Vector_set___redArg(v_xs_3886_, v_i_3887_, v_x_3888_);
    leanh::lean_dec(v_i_3887_);
    return v_res_3889_;
}
pub unsafe fn l_Vector_set(
    mut v_00_u03b1_3890_: *mut leanh::LeanObject,
    mut v_n_3891_: *mut leanh::LeanObject,
    mut v_xs_3892_: *mut leanh::LeanObject,
    mut v_i_3893_: *mut leanh::LeanObject,
    mut v_x_3894_: *mut leanh::LeanObject,
    mut v_h_3895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3896_ = lean_array_fset(v_xs_3892_, v_i_3893_, v_x_3894_);
    return v___x_3896_;
}
pub unsafe fn l_Vector_set___boxed(
    mut v_00_u03b1_3897_: *mut leanh::LeanObject,
    mut v_n_3898_: *mut leanh::LeanObject,
    mut v_xs_3899_: *mut leanh::LeanObject,
    mut v_i_3900_: *mut leanh::LeanObject,
    mut v_x_3901_: *mut leanh::LeanObject,
    mut v_h_3902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3903_ = l_Vector_set(
        v_00_u03b1_3897_,
        v_n_3898_,
        v_xs_3899_,
        v_i_3900_,
        v_x_3901_,
        v_h_3902_,
    );
    leanh::lean_dec(v_i_3900_);
    leanh::lean_dec(v_n_3898_);
    return v_res_3903_;
}
pub unsafe fn l_Vector_setIfInBounds___redArg(
    mut v_xs_3904_: *mut leanh::LeanObject,
    mut v_i_3905_: *mut leanh::LeanObject,
    mut v_x_3906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: u8 = 0;
    v___x_3907_ = lean_array_get_size(v_xs_3904_);
    v___x_3908_ = lean_nat_dec_lt(v_i_3905_, v___x_3907_);
    if v___x_3908_ == 0 {
        leanh::lean_dec(v_x_3906_);
        return v_xs_3904_;
    } else {
        let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3909_ = lean_array_fset(v_xs_3904_, v_i_3905_, v_x_3906_);
        return v___x_3909_;
    }
}
pub unsafe fn l_Vector_setIfInBounds___redArg___boxed(
    mut v_xs_3910_: *mut leanh::LeanObject,
    mut v_i_3911_: *mut leanh::LeanObject,
    mut v_x_3912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3913_ = l_Vector_setIfInBounds___redArg(v_xs_3910_, v_i_3911_, v_x_3912_);
    leanh::lean_dec(v_i_3911_);
    return v_res_3913_;
}
pub unsafe fn l_Vector_setIfInBounds(
    mut v_00_u03b1_3914_: *mut leanh::LeanObject,
    mut v_n_3915_: *mut leanh::LeanObject,
    mut v_xs_3916_: *mut leanh::LeanObject,
    mut v_i_3917_: *mut leanh::LeanObject,
    mut v_x_3918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: u8 = 0;
    v___x_3919_ = lean_array_get_size(v_xs_3916_);
    v___x_3920_ = lean_nat_dec_lt(v_i_3917_, v___x_3919_);
    if v___x_3920_ == 0 {
        leanh::lean_dec(v_x_3918_);
        return v_xs_3916_;
    } else {
        let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3921_ = lean_array_fset(v_xs_3916_, v_i_3917_, v_x_3918_);
        return v___x_3921_;
    }
}
pub unsafe fn l_Vector_setIfInBounds___boxed(
    mut v_00_u03b1_3922_: *mut leanh::LeanObject,
    mut v_n_3923_: *mut leanh::LeanObject,
    mut v_xs_3924_: *mut leanh::LeanObject,
    mut v_i_3925_: *mut leanh::LeanObject,
    mut v_x_3926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3927_ = l_Vector_setIfInBounds(
        v_00_u03b1_3922_,
        v_n_3923_,
        v_xs_3924_,
        v_i_3925_,
        v_x_3926_,
    );
    leanh::lean_dec(v_i_3925_);
    leanh::lean_dec(v_n_3923_);
    return v_res_3927_;
}
pub unsafe fn l_Vector_set_x21___redArg(
    mut v_xs_3928_: *mut leanh::LeanObject,
    mut v_i_3929_: *mut leanh::LeanObject,
    mut v_x_3930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3931_ = lean_array_set(v_xs_3928_, v_i_3929_, v_x_3930_);
    return v___x_3931_;
}
pub unsafe fn l_Vector_set_x21___redArg___boxed(
    mut v_xs_3932_: *mut leanh::LeanObject,
    mut v_i_3933_: *mut leanh::LeanObject,
    mut v_x_3934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3935_ = l_Vector_set_x21___redArg(v_xs_3932_, v_i_3933_, v_x_3934_);
    leanh::lean_dec(v_i_3933_);
    return v_res_3935_;
}
pub unsafe fn l_Vector_set_x21(
    mut v_00_u03b1_3936_: *mut leanh::LeanObject,
    mut v_n_3937_: *mut leanh::LeanObject,
    mut v_xs_3938_: *mut leanh::LeanObject,
    mut v_i_3939_: *mut leanh::LeanObject,
    mut v_x_3940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3941_ = lean_array_set(v_xs_3938_, v_i_3939_, v_x_3940_);
    return v___x_3941_;
}
pub unsafe fn l_Vector_set_x21___boxed(
    mut v_00_u03b1_3942_: *mut leanh::LeanObject,
    mut v_n_3943_: *mut leanh::LeanObject,
    mut v_xs_3944_: *mut leanh::LeanObject,
    mut v_i_3945_: *mut leanh::LeanObject,
    mut v_x_3946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3947_ = l_Vector_set_x21(
        v_00_u03b1_3942_,
        v_n_3943_,
        v_xs_3944_,
        v_i_3945_,
        v_x_3946_,
    );
    leanh::lean_dec(v_i_3945_);
    leanh::lean_dec(v_n_3943_);
    return v_res_3947_;
}
pub unsafe fn l_Vector_foldlM___redArg(
    mut v_inst_3948_: *mut leanh::LeanObject,
    mut v_f_3949_: *mut leanh::LeanObject,
    mut v_b_3950_: *mut leanh::LeanObject,
    mut v_xs_3951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: u8 = 0;
    v___x_3952_ = leanh::lean_unsigned_to_nat(0);
    v___x_3953_ = lean_array_get_size(v_xs_3951_);
    v___x_3954_ = lean_nat_dec_lt(v___x_3952_, v___x_3953_);
    if v___x_3954_ == 0 {
        let mut v_toApplicative_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_3951_);
        leanh::lean_dec(v_f_3949_);
        v_toApplicative_3955_ = leanh::lean_ctor_get(v_inst_3948_, 0);
        leanh::lean_inc_ref(v_toApplicative_3955_);
        leanh::lean_dec_ref(v_inst_3948_);
        v_toPure_3956_ = leanh::lean_ctor_get(v_toApplicative_3955_, 1);
        leanh::lean_inc(v_toPure_3956_);
        leanh::lean_dec_ref(v_toApplicative_3955_);
        v___x_3957_ =
            leanh::lean_apply_2(v_toPure_3956_, leanh::lean_box(0), v_b_3950_);
        return v___x_3957_;
    } else {
        let mut v___x_3958_: u8 = 0;
        v___x_3958_ = lean_nat_dec_le(v___x_3953_, v___x_3953_);
        if v___x_3958_ == 0 {
            if v___x_3954_ == 0 {
                let mut v_toApplicative_3959_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_xs_3951_);
                leanh::lean_dec(v_f_3949_);
                v_toApplicative_3959_ = leanh::lean_ctor_get(v_inst_3948_, 0);
                leanh::lean_inc_ref(v_toApplicative_3959_);
                leanh::lean_dec_ref(v_inst_3948_);
                v_toPure_3960_ = leanh::lean_ctor_get(v_toApplicative_3959_, 1);
                leanh::lean_inc(v_toPure_3960_);
                leanh::lean_dec_ref(v_toApplicative_3959_);
                v___x_3961_ = leanh::lean_apply_2(
                    v_toPure_3960_,
                    leanh::lean_box(0),
                    v_b_3950_,
                );
                return v___x_3961_;
            } else {
                let mut v___x_3962_: usize = 0;
                let mut v___x_3963_: usize = 0;
                let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3962_ = 0usize;
                v___x_3963_ = lean_usize_of_nat(v___x_3953_);
                v___x_3964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_3948_,
                    v_f_3949_,
                    v_xs_3951_,
                    v___x_3962_,
                    v___x_3963_,
                    v_b_3950_,
                );
                return v___x_3964_;
            }
        } else {
            let mut v___x_3965_: usize = 0;
            let mut v___x_3966_: usize = 0;
            let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3965_ = 0usize;
            v___x_3966_ = lean_usize_of_nat(v___x_3953_);
            v___x_3967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_3948_,
                v_f_3949_,
                v_xs_3951_,
                v___x_3965_,
                v___x_3966_,
                v_b_3950_,
            );
            return v___x_3967_;
        }
    }
}
pub unsafe fn l_Vector_foldlM(
    mut v_m_3968_: *mut leanh::LeanObject,
    mut v_00_u03b2_3969_: *mut leanh::LeanObject,
    mut v_00_u03b1_3970_: *mut leanh::LeanObject,
    mut v_n_3971_: *mut leanh::LeanObject,
    mut v_inst_3972_: *mut leanh::LeanObject,
    mut v_f_3973_: *mut leanh::LeanObject,
    mut v_b_3974_: *mut leanh::LeanObject,
    mut v_xs_3975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: u8 = 0;
    v___x_3976_ = leanh::lean_unsigned_to_nat(0);
    v___x_3977_ = lean_array_get_size(v_xs_3975_);
    v___x_3978_ = lean_nat_dec_lt(v___x_3976_, v___x_3977_);
    if v___x_3978_ == 0 {
        let mut v_toApplicative_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_3975_);
        leanh::lean_dec(v_f_3973_);
        v_toApplicative_3979_ = leanh::lean_ctor_get(v_inst_3972_, 0);
        leanh::lean_inc_ref(v_toApplicative_3979_);
        leanh::lean_dec_ref(v_inst_3972_);
        v_toPure_3980_ = leanh::lean_ctor_get(v_toApplicative_3979_, 1);
        leanh::lean_inc(v_toPure_3980_);
        leanh::lean_dec_ref(v_toApplicative_3979_);
        v___x_3981_ =
            leanh::lean_apply_2(v_toPure_3980_, leanh::lean_box(0), v_b_3974_);
        return v___x_3981_;
    } else {
        let mut v___x_3982_: u8 = 0;
        v___x_3982_ = lean_nat_dec_le(v___x_3977_, v___x_3977_);
        if v___x_3982_ == 0 {
            if v___x_3978_ == 0 {
                let mut v_toApplicative_3983_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_xs_3975_);
                leanh::lean_dec(v_f_3973_);
                v_toApplicative_3983_ = leanh::lean_ctor_get(v_inst_3972_, 0);
                leanh::lean_inc_ref(v_toApplicative_3983_);
                leanh::lean_dec_ref(v_inst_3972_);
                v_toPure_3984_ = leanh::lean_ctor_get(v_toApplicative_3983_, 1);
                leanh::lean_inc(v_toPure_3984_);
                leanh::lean_dec_ref(v_toApplicative_3983_);
                v___x_3985_ = leanh::lean_apply_2(
                    v_toPure_3984_,
                    leanh::lean_box(0),
                    v_b_3974_,
                );
                return v___x_3985_;
            } else {
                let mut v___x_3986_: usize = 0;
                let mut v___x_3987_: usize = 0;
                let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3986_ = 0usize;
                v___x_3987_ = lean_usize_of_nat(v___x_3977_);
                v___x_3988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_3972_,
                    v_f_3973_,
                    v_xs_3975_,
                    v___x_3986_,
                    v___x_3987_,
                    v_b_3974_,
                );
                return v___x_3988_;
            }
        } else {
            let mut v___x_3989_: usize = 0;
            let mut v___x_3990_: usize = 0;
            let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3989_ = 0usize;
            v___x_3990_ = lean_usize_of_nat(v___x_3977_);
            v___x_3991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_3972_,
                v_f_3973_,
                v_xs_3975_,
                v___x_3989_,
                v___x_3990_,
                v_b_3974_,
            );
            return v___x_3991_;
        }
    }
}
pub unsafe fn l_Vector_foldlM___boxed(
    mut v_m_3992_: *mut leanh::LeanObject,
    mut v_00_u03b2_3993_: *mut leanh::LeanObject,
    mut v_00_u03b1_3994_: *mut leanh::LeanObject,
    mut v_n_3995_: *mut leanh::LeanObject,
    mut v_inst_3996_: *mut leanh::LeanObject,
    mut v_f_3997_: *mut leanh::LeanObject,
    mut v_b_3998_: *mut leanh::LeanObject,
    mut v_xs_3999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4000_ = l_Vector_foldlM(
        v_m_3992_,
        v_00_u03b2_3993_,
        v_00_u03b1_3994_,
        v_n_3995_,
        v_inst_3996_,
        v_f_3997_,
        v_b_3998_,
        v_xs_3999_,
    );
    leanh::lean_dec(v_n_3995_);
    return v_res_4000_;
}
pub unsafe fn l_Vector_foldrM___redArg(
    mut v_inst_4001_: *mut leanh::LeanObject,
    mut v_f_4002_: *mut leanh::LeanObject,
    mut v_b_4003_: *mut leanh::LeanObject,
    mut v_xs_4004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: u8 = 0;
    v___x_4005_ = lean_array_get_size(v_xs_4004_);
    v___x_4006_ = leanh::lean_unsigned_to_nat(0);
    v___x_4007_ = lean_nat_dec_lt(v___x_4006_, v___x_4005_);
    if v___x_4007_ == 0 {
        let mut v_toApplicative_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_4004_);
        leanh::lean_dec(v_f_4002_);
        v_toApplicative_4008_ = leanh::lean_ctor_get(v_inst_4001_, 0);
        leanh::lean_inc_ref(v_toApplicative_4008_);
        leanh::lean_dec_ref(v_inst_4001_);
        v_toPure_4009_ = leanh::lean_ctor_get(v_toApplicative_4008_, 1);
        leanh::lean_inc(v_toPure_4009_);
        leanh::lean_dec_ref(v_toApplicative_4008_);
        v___x_4010_ =
            leanh::lean_apply_2(v_toPure_4009_, leanh::lean_box(0), v_b_4003_);
        return v___x_4010_;
    } else {
        let mut v___x_4011_: usize = 0;
        let mut v___x_4012_: usize = 0;
        let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4011_ = lean_usize_of_nat(v___x_4005_);
        v___x_4012_ = 0usize;
        v___x_4013_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_4001_,
            v_f_4002_,
            v_xs_4004_,
            v___x_4011_,
            v___x_4012_,
            v_b_4003_,
        );
        return v___x_4013_;
    }
}
pub unsafe fn l_Vector_foldrM(
    mut v_m_4014_: *mut leanh::LeanObject,
    mut v_00_u03b1_4015_: *mut leanh::LeanObject,
    mut v_00_u03b2_4016_: *mut leanh::LeanObject,
    mut v_n_4017_: *mut leanh::LeanObject,
    mut v_inst_4018_: *mut leanh::LeanObject,
    mut v_f_4019_: *mut leanh::LeanObject,
    mut v_b_4020_: *mut leanh::LeanObject,
    mut v_xs_4021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: u8 = 0;
    v___x_4022_ = lean_array_get_size(v_xs_4021_);
    v___x_4023_ = leanh::lean_unsigned_to_nat(0);
    v___x_4024_ = lean_nat_dec_lt(v___x_4023_, v___x_4022_);
    if v___x_4024_ == 0 {
        let mut v_toApplicative_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_4021_);
        leanh::lean_dec(v_f_4019_);
        v_toApplicative_4025_ = leanh::lean_ctor_get(v_inst_4018_, 0);
        leanh::lean_inc_ref(v_toApplicative_4025_);
        leanh::lean_dec_ref(v_inst_4018_);
        v_toPure_4026_ = leanh::lean_ctor_get(v_toApplicative_4025_, 1);
        leanh::lean_inc(v_toPure_4026_);
        leanh::lean_dec_ref(v_toApplicative_4025_);
        v___x_4027_ =
            leanh::lean_apply_2(v_toPure_4026_, leanh::lean_box(0), v_b_4020_);
        return v___x_4027_;
    } else {
        let mut v___x_4028_: usize = 0;
        let mut v___x_4029_: usize = 0;
        let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4028_ = lean_usize_of_nat(v___x_4022_);
        v___x_4029_ = 0usize;
        v___x_4030_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_4018_,
            v_f_4019_,
            v_xs_4021_,
            v___x_4028_,
            v___x_4029_,
            v_b_4020_,
        );
        return v___x_4030_;
    }
}
pub unsafe fn l_Vector_foldrM___boxed(
    mut v_m_4031_: *mut leanh::LeanObject,
    mut v_00_u03b1_4032_: *mut leanh::LeanObject,
    mut v_00_u03b2_4033_: *mut leanh::LeanObject,
    mut v_n_4034_: *mut leanh::LeanObject,
    mut v_inst_4035_: *mut leanh::LeanObject,
    mut v_f_4036_: *mut leanh::LeanObject,
    mut v_b_4037_: *mut leanh::LeanObject,
    mut v_xs_4038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4039_ = l_Vector_foldrM(
        v_m_4031_,
        v_00_u03b1_4032_,
        v_00_u03b2_4033_,
        v_n_4034_,
        v_inst_4035_,
        v_f_4036_,
        v_b_4037_,
        v_xs_4038_,
    );
    leanh::lean_dec(v_n_4034_);
    return v_res_4039_;
}
pub unsafe fn l_Vector_foldl___redArg___lam__0(
    mut v_f_4040_: *mut leanh::LeanObject,
    mut v_x1_4041_: *mut leanh::LeanObject,
    mut v_x2_4042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4043_ = leanh::lean_apply_2(v_f_4040_, v_x1_4041_, v_x2_4042_);
    return v___x_4043_;
}
pub unsafe fn l_Vector_foldl___redArg(
    mut v_f_4063_: *mut leanh::LeanObject,
    mut v_b_4064_: *mut leanh::LeanObject,
    mut v_xs_4065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: u8 = 0;
    v___x_4066_ = leanh::lean_unsigned_to_nat(0);
    v___x_4067_ = lean_array_get_size(v_xs_4065_);
    v___x_4068_ = l_Vector_foldl___redArg___closed__9;
    v___x_4069_ = lean_nat_dec_lt(v___x_4066_, v___x_4067_);
    if v___x_4069_ == 0 {
        leanh::lean_dec_ref(v_xs_4065_);
        leanh::lean_dec(v_f_4063_);
        return v_b_4064_;
    } else {
        let mut v___f_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4071_: u8 = 0;
        v___f_4070_ = leanh::lean_alloc_closure(
            l_Vector_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_4070_, 0, v_f_4063_);
        v___x_4071_ = lean_nat_dec_le(v___x_4067_, v___x_4067_);
        if v___x_4071_ == 0 {
            if v___x_4069_ == 0 {
                leanh::lean_dec_ref(v___f_4070_);
                leanh::lean_dec_ref(v_xs_4065_);
                return v_b_4064_;
            } else {
                let mut v___x_4072_: usize = 0;
                let mut v___x_4073_: usize = 0;
                let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4072_ = 0usize;
                v___x_4073_ = lean_usize_of_nat(v___x_4067_);
                v___x_4074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_4068_,
                    v___f_4070_,
                    v_xs_4065_,
                    v___x_4072_,
                    v___x_4073_,
                    v_b_4064_,
                );
                return v___x_4074_;
            }
        } else {
            let mut v___x_4075_: usize = 0;
            let mut v___x_4076_: usize = 0;
            let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4075_ = 0usize;
            v___x_4076_ = lean_usize_of_nat(v___x_4067_);
            v___x_4077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_4068_,
                v___f_4070_,
                v_xs_4065_,
                v___x_4075_,
                v___x_4076_,
                v_b_4064_,
            );
            return v___x_4077_;
        }
    }
}
pub unsafe fn l_Vector_foldl(
    mut v_00_u03b2_4078_: *mut leanh::LeanObject,
    mut v_00_u03b1_4079_: *mut leanh::LeanObject,
    mut v_n_4080_: *mut leanh::LeanObject,
    mut v_f_4081_: *mut leanh::LeanObject,
    mut v_b_4082_: *mut leanh::LeanObject,
    mut v_xs_4083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: u8 = 0;
    v___x_4084_ = leanh::lean_unsigned_to_nat(0);
    v___x_4085_ = lean_array_get_size(v_xs_4083_);
    v___x_4086_ = l_Vector_foldl___redArg___closed__9;
    v___x_4087_ = lean_nat_dec_lt(v___x_4084_, v___x_4085_);
    if v___x_4087_ == 0 {
        leanh::lean_dec_ref(v_xs_4083_);
        leanh::lean_dec(v_f_4081_);
        return v_b_4082_;
    } else {
        let mut v___f_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4089_: u8 = 0;
        v___f_4088_ = leanh::lean_alloc_closure(
            l_Vector_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_4088_, 0, v_f_4081_);
        v___x_4089_ = lean_nat_dec_le(v___x_4085_, v___x_4085_);
        if v___x_4089_ == 0 {
            if v___x_4087_ == 0 {
                leanh::lean_dec_ref(v___f_4088_);
                leanh::lean_dec_ref(v_xs_4083_);
                return v_b_4082_;
            } else {
                let mut v___x_4090_: usize = 0;
                let mut v___x_4091_: usize = 0;
                let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4090_ = 0usize;
                v___x_4091_ = lean_usize_of_nat(v___x_4085_);
                v___x_4092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_4086_,
                    v___f_4088_,
                    v_xs_4083_,
                    v___x_4090_,
                    v___x_4091_,
                    v_b_4082_,
                );
                return v___x_4092_;
            }
        } else {
            let mut v___x_4093_: usize = 0;
            let mut v___x_4094_: usize = 0;
            let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4093_ = 0usize;
            v___x_4094_ = lean_usize_of_nat(v___x_4085_);
            v___x_4095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_4086_,
                v___f_4088_,
                v_xs_4083_,
                v___x_4093_,
                v___x_4094_,
                v_b_4082_,
            );
            return v___x_4095_;
        }
    }
}
pub unsafe fn l_Vector_foldl___boxed(
    mut v_00_u03b2_4096_: *mut leanh::LeanObject,
    mut v_00_u03b1_4097_: *mut leanh::LeanObject,
    mut v_n_4098_: *mut leanh::LeanObject,
    mut v_f_4099_: *mut leanh::LeanObject,
    mut v_b_4100_: *mut leanh::LeanObject,
    mut v_xs_4101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4102_ = l_Vector_foldl(
        v_00_u03b2_4096_,
        v_00_u03b1_4097_,
        v_n_4098_,
        v_f_4099_,
        v_b_4100_,
        v_xs_4101_,
    );
    leanh::lean_dec(v_n_4098_);
    return v_res_4102_;
}
pub unsafe fn l_Vector_foldr___redArg(
    mut v_f_4103_: *mut leanh::LeanObject,
    mut v_b_4104_: *mut leanh::LeanObject,
    mut v_xs_4105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: u8 = 0;
    v___x_4106_ = lean_array_get_size(v_xs_4105_);
    v___x_4107_ = leanh::lean_unsigned_to_nat(0);
    v___x_4108_ = l_Vector_foldl___redArg___closed__9;
    v___x_4109_ = lean_nat_dec_lt(v___x_4107_, v___x_4106_);
    if v___x_4109_ == 0 {
        leanh::lean_dec_ref(v_xs_4105_);
        leanh::lean_dec(v_f_4103_);
        return v_b_4104_;
    } else {
        let mut v___f_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4111_: usize = 0;
        let mut v___x_4112_: usize = 0;
        let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4110_ = leanh::lean_alloc_closure(
            l_Vector_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_4110_, 0, v_f_4103_);
        v___x_4111_ = lean_usize_of_nat(v___x_4106_);
        v___x_4112_ = 0usize;
        v___x_4113_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4108_,
            v___f_4110_,
            v_xs_4105_,
            v___x_4111_,
            v___x_4112_,
            v_b_4104_,
        );
        return v___x_4113_;
    }
}
pub unsafe fn l_Vector_foldr(
    mut v_00_u03b1_4114_: *mut leanh::LeanObject,
    mut v_00_u03b2_4115_: *mut leanh::LeanObject,
    mut v_n_4116_: *mut leanh::LeanObject,
    mut v_f_4117_: *mut leanh::LeanObject,
    mut v_b_4118_: *mut leanh::LeanObject,
    mut v_xs_4119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: u8 = 0;
    v___x_4120_ = lean_array_get_size(v_xs_4119_);
    v___x_4121_ = leanh::lean_unsigned_to_nat(0);
    v___x_4122_ = l_Vector_foldl___redArg___closed__9;
    v___x_4123_ = lean_nat_dec_lt(v___x_4121_, v___x_4120_);
    if v___x_4123_ == 0 {
        leanh::lean_dec_ref(v_xs_4119_);
        leanh::lean_dec(v_f_4117_);
        return v_b_4118_;
    } else {
        let mut v___f_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4125_: usize = 0;
        let mut v___x_4126_: usize = 0;
        let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4124_ = leanh::lean_alloc_closure(
            l_Vector_foldl___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_4124_, 0, v_f_4117_);
        v___x_4125_ = lean_usize_of_nat(v___x_4120_);
        v___x_4126_ = 0usize;
        v___x_4127_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4122_,
            v___f_4124_,
            v_xs_4119_,
            v___x_4125_,
            v___x_4126_,
            v_b_4118_,
        );
        return v___x_4127_;
    }
}
pub unsafe fn l_Vector_foldr___boxed(
    mut v_00_u03b1_4128_: *mut leanh::LeanObject,
    mut v_00_u03b2_4129_: *mut leanh::LeanObject,
    mut v_n_4130_: *mut leanh::LeanObject,
    mut v_f_4131_: *mut leanh::LeanObject,
    mut v_b_4132_: *mut leanh::LeanObject,
    mut v_xs_4133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4134_ = l_Vector_foldr(
        v_00_u03b1_4128_,
        v_00_u03b2_4129_,
        v_n_4130_,
        v_f_4131_,
        v_b_4132_,
        v_xs_4133_,
    );
    leanh::lean_dec(v_n_4130_);
    return v_res_4134_;
}
pub unsafe fn l_Vector_append___redArg(
    mut v_xs_4135_: *mut leanh::LeanObject,
    mut v_ys_4136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4137_ = l_Array_append___redArg(v_xs_4135_, v_ys_4136_);
    return v___x_4137_;
}
pub unsafe fn l_Vector_append___redArg___boxed(
    mut v_xs_4138_: *mut leanh::LeanObject,
    mut v_ys_4139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4140_ = l_Vector_append___redArg(v_xs_4138_, v_ys_4139_);
    leanh::lean_dec_ref(v_ys_4139_);
    return v_res_4140_;
}
pub unsafe fn l_Vector_append(
    mut v_00_u03b1_4141_: *mut leanh::LeanObject,
    mut v_n_4142_: *mut leanh::LeanObject,
    mut v_m_4143_: *mut leanh::LeanObject,
    mut v_xs_4144_: *mut leanh::LeanObject,
    mut v_ys_4145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4146_ = l_Array_append___redArg(v_xs_4144_, v_ys_4145_);
    return v___x_4146_;
}
pub unsafe fn l_Vector_append___boxed(
    mut v_00_u03b1_4147_: *mut leanh::LeanObject,
    mut v_n_4148_: *mut leanh::LeanObject,
    mut v_m_4149_: *mut leanh::LeanObject,
    mut v_xs_4150_: *mut leanh::LeanObject,
    mut v_ys_4151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4152_ = l_Vector_append(
        v_00_u03b1_4147_,
        v_n_4148_,
        v_m_4149_,
        v_xs_4150_,
        v_ys_4151_,
    );
    leanh::lean_dec_ref(v_ys_4151_);
    leanh::lean_dec(v_m_4149_);
    leanh::lean_dec(v_n_4148_);
    return v_res_4152_;
}
pub unsafe fn l_Vector_instHAppendHAddNat___redArg(
    mut v_n_4153_: *mut leanh::LeanObject,
    mut v_m_4154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4155_ =
        leanh::lean_alloc_closure(l_Vector_append___boxed as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_4155_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4155_, 1, v_n_4153_);
    leanh::lean_closure_set(v___x_4155_, 2, v_m_4154_);
    return v___x_4155_;
}
pub unsafe fn l_Vector_instHAppendHAddNat(
    mut v_00_u03b1_4156_: *mut leanh::LeanObject,
    mut v_n_4157_: *mut leanh::LeanObject,
    mut v_m_4158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4159_ =
        leanh::lean_alloc_closure(l_Vector_append___boxed as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_4159_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4159_, 1, v_n_4157_);
    leanh::lean_closure_set(v___x_4159_, 2, v_m_4158_);
    return v___x_4159_;
}
pub unsafe fn l_Vector_cast___redArg(
    mut v_xs_4160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_xs_4160_);
    return v_xs_4160_;
}
pub unsafe fn l_Vector_cast___redArg___boxed(
    mut v_xs_4161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4162_ = l_Vector_cast___redArg(v_xs_4161_);
    leanh::lean_dec_ref(v_xs_4161_);
    return v_res_4162_;
}
pub unsafe fn l_Vector_cast(
    mut v_n_4163_: *mut leanh::LeanObject,
    mut v_m_4164_: *mut leanh::LeanObject,
    mut v_00_u03b1_4165_: *mut leanh::LeanObject,
    mut v_h_4166_: *mut leanh::LeanObject,
    mut v_xs_4167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_xs_4167_);
    return v_xs_4167_;
}
pub unsafe fn l_Vector_cast___boxed(
    mut v_n_4168_: *mut leanh::LeanObject,
    mut v_m_4169_: *mut leanh::LeanObject,
    mut v_00_u03b1_4170_: *mut leanh::LeanObject,
    mut v_h_4171_: *mut leanh::LeanObject,
    mut v_xs_4172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4173_ = l_Vector_cast(
        v_n_4168_,
        v_m_4169_,
        v_00_u03b1_4170_,
        v_h_4171_,
        v_xs_4172_,
    );
    leanh::lean_dec_ref(v_xs_4172_);
    leanh::lean_dec(v_m_4169_);
    leanh::lean_dec(v_n_4168_);
    return v_res_4173_;
}
pub unsafe fn l_Vector_extract___redArg(
    mut v_xs_4174_: *mut leanh::LeanObject,
    mut v_start_4175_: *mut leanh::LeanObject,
    mut v_stop_4176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4177_ = l_Array_extract___redArg(v_xs_4174_, v_start_4175_, v_stop_4176_);
    return v___x_4177_;
}
pub unsafe fn l_Vector_extract___redArg___boxed(
    mut v_xs_4178_: *mut leanh::LeanObject,
    mut v_start_4179_: *mut leanh::LeanObject,
    mut v_stop_4180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4181_ = l_Vector_extract___redArg(v_xs_4178_, v_start_4179_, v_stop_4180_);
    leanh::lean_dec_ref(v_xs_4178_);
    return v_res_4181_;
}
pub unsafe fn l_Vector_extract(
    mut v_00_u03b1_4182_: *mut leanh::LeanObject,
    mut v_n_4183_: *mut leanh::LeanObject,
    mut v_xs_4184_: *mut leanh::LeanObject,
    mut v_start_4185_: *mut leanh::LeanObject,
    mut v_stop_4186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4187_ = l_Array_extract___redArg(v_xs_4184_, v_start_4185_, v_stop_4186_);
    return v___x_4187_;
}
pub unsafe fn l_Vector_extract___boxed(
    mut v_00_u03b1_4188_: *mut leanh::LeanObject,
    mut v_n_4189_: *mut leanh::LeanObject,
    mut v_xs_4190_: *mut leanh::LeanObject,
    mut v_start_4191_: *mut leanh::LeanObject,
    mut v_stop_4192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4193_ = l_Vector_extract(
        v_00_u03b1_4188_,
        v_n_4189_,
        v_xs_4190_,
        v_start_4191_,
        v_stop_4192_,
    );
    leanh::lean_dec_ref(v_xs_4190_);
    leanh::lean_dec(v_n_4189_);
    return v_res_4193_;
}
pub unsafe fn l_Vector_take___redArg(
    mut v_n_4194_: *mut leanh::LeanObject,
    mut v_xs_4195_: *mut leanh::LeanObject,
    mut v_i_4196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4197_ = leanh::lean_unsigned_to_nat(0);
    v___x_4198_ = l_Array_extract___redArg(v_xs_4195_, v___x_4197_, v_i_4196_);
    return v___x_4198_;
}
pub unsafe fn l_Vector_take___redArg___boxed(
    mut v_n_4199_: *mut leanh::LeanObject,
    mut v_xs_4200_: *mut leanh::LeanObject,
    mut v_i_4201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4202_ = l_Vector_take___redArg(v_n_4199_, v_xs_4200_, v_i_4201_);
    leanh::lean_dec_ref(v_xs_4200_);
    leanh::lean_dec(v_n_4199_);
    return v_res_4202_;
}
pub unsafe fn l_Vector_take(
    mut v_00_u03b1_4203_: *mut leanh::LeanObject,
    mut v_n_4204_: *mut leanh::LeanObject,
    mut v_xs_4205_: *mut leanh::LeanObject,
    mut v_i_4206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4207_ = leanh::lean_unsigned_to_nat(0);
    v___x_4208_ = l_Array_extract___redArg(v_xs_4205_, v___x_4207_, v_i_4206_);
    return v___x_4208_;
}
pub unsafe fn l_Vector_take___boxed(
    mut v_00_u03b1_4209_: *mut leanh::LeanObject,
    mut v_n_4210_: *mut leanh::LeanObject,
    mut v_xs_4211_: *mut leanh::LeanObject,
    mut v_i_4212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4213_ = l_Vector_take(v_00_u03b1_4209_, v_n_4210_, v_xs_4211_, v_i_4212_);
    leanh::lean_dec_ref(v_xs_4211_);
    leanh::lean_dec(v_n_4210_);
    return v_res_4213_;
}
pub unsafe fn l_Vector_drop___redArg(
    mut v_xs_4214_: *mut leanh::LeanObject,
    mut v_i_4215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4216_ = lean_array_get_size(v_xs_4214_);
    v___x_4217_ = l_Array_extract___redArg(v_xs_4214_, v_i_4215_, v___x_4216_);
    return v___x_4217_;
}
pub unsafe fn l_Vector_drop___redArg___boxed(
    mut v_xs_4218_: *mut leanh::LeanObject,
    mut v_i_4219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4220_ = l_Vector_drop___redArg(v_xs_4218_, v_i_4219_);
    leanh::lean_dec_ref(v_xs_4218_);
    return v_res_4220_;
}
pub unsafe fn l_Vector_drop(
    mut v_00_u03b1_4221_: *mut leanh::LeanObject,
    mut v_n_4222_: *mut leanh::LeanObject,
    mut v_xs_4223_: *mut leanh::LeanObject,
    mut v_i_4224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4225_ = lean_array_get_size(v_xs_4223_);
    v___x_4226_ = l_Array_extract___redArg(v_xs_4223_, v_i_4224_, v___x_4225_);
    return v___x_4226_;
}
pub unsafe fn l_Vector_drop___boxed(
    mut v_00_u03b1_4227_: *mut leanh::LeanObject,
    mut v_n_4228_: *mut leanh::LeanObject,
    mut v_xs_4229_: *mut leanh::LeanObject,
    mut v_i_4230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4231_ = l_Vector_drop(v_00_u03b1_4227_, v_n_4228_, v_xs_4229_, v_i_4230_);
    leanh::lean_dec_ref(v_xs_4229_);
    leanh::lean_dec(v_n_4228_);
    return v_res_4231_;
}
pub unsafe fn l_Vector_shrink___redArg(
    mut v_xs_4232_: *mut leanh::LeanObject,
    mut v_i_4233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4234_ = l_Array_shrink___redArg(v_xs_4232_, v_i_4233_);
    return v___x_4234_;
}
pub unsafe fn l_Vector_shrink___redArg___boxed(
    mut v_xs_4235_: *mut leanh::LeanObject,
    mut v_i_4236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4237_ = l_Vector_shrink___redArg(v_xs_4235_, v_i_4236_);
    leanh::lean_dec(v_i_4236_);
    return v_res_4237_;
}
pub unsafe fn l_Vector_shrink(
    mut v_00_u03b1_4238_: *mut leanh::LeanObject,
    mut v_n_4239_: *mut leanh::LeanObject,
    mut v_xs_4240_: *mut leanh::LeanObject,
    mut v_i_4241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4242_ = l_Array_shrink___redArg(v_xs_4240_, v_i_4241_);
    return v___x_4242_;
}
pub unsafe fn l_Vector_shrink___boxed(
    mut v_00_u03b1_4243_: *mut leanh::LeanObject,
    mut v_n_4244_: *mut leanh::LeanObject,
    mut v_xs_4245_: *mut leanh::LeanObject,
    mut v_i_4246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4247_ = l_Vector_shrink(v_00_u03b1_4243_, v_n_4244_, v_xs_4245_, v_i_4246_);
    leanh::lean_dec(v_i_4246_);
    leanh::lean_dec(v_n_4244_);
    return v_res_4247_;
}
pub unsafe fn l_Vector_map___redArg___lam__0(
    mut v_f_4248_: *mut leanh::LeanObject,
    mut v_x_4249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4250_ = leanh::lean_apply_1(v_f_4248_, v_x_4249_);
    return v___x_4250_;
}
pub unsafe fn l_Vector_map___redArg(
    mut v_f_4251_: *mut leanh::LeanObject,
    mut v_xs_4252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4255_: usize = 0;
    let mut v___x_4256_: usize = 0;
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4253_ = leanh::lean_alloc_closure(
        l_Vector_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4253_, 0, v_f_4251_);
    v___x_4254_ = l_Vector_foldl___redArg___closed__9;
    v_sz_4255_ = lean_array_size(v_xs_4252_);
    v___x_4256_ = 0usize;
    v___x_4257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4254_,
        v___f_4253_,
        v_sz_4255_,
        v___x_4256_,
        v_xs_4252_,
    );
    return v___x_4257_;
}
pub unsafe fn l_Vector_map(
    mut v_00_u03b1_4258_: *mut leanh::LeanObject,
    mut v_00_u03b2_4259_: *mut leanh::LeanObject,
    mut v_n_4260_: *mut leanh::LeanObject,
    mut v_f_4261_: *mut leanh::LeanObject,
    mut v_xs_4262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4265_: usize = 0;
    let mut v___x_4266_: usize = 0;
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4263_ = leanh::lean_alloc_closure(
        l_Vector_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4263_, 0, v_f_4261_);
    v___x_4264_ = l_Vector_foldl___redArg___closed__9;
    v_sz_4265_ = lean_array_size(v_xs_4262_);
    v___x_4266_ = 0usize;
    v___x_4267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4264_,
        v___f_4263_,
        v_sz_4265_,
        v___x_4266_,
        v_xs_4262_,
    );
    return v___x_4267_;
}
pub unsafe fn l_Vector_map___boxed(
    mut v_00_u03b1_4268_: *mut leanh::LeanObject,
    mut v_00_u03b2_4269_: *mut leanh::LeanObject,
    mut v_n_4270_: *mut leanh::LeanObject,
    mut v_f_4271_: *mut leanh::LeanObject,
    mut v_xs_4272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4273_ = l_Vector_map(
        v_00_u03b1_4268_,
        v_00_u03b2_4269_,
        v_n_4270_,
        v_f_4271_,
        v_xs_4272_,
    );
    leanh::lean_dec(v_n_4270_);
    return v_res_4273_;
}
pub unsafe fn l_Vector_mapIdx___redArg___lam__0(
    mut v_f_4274_: *mut leanh::LeanObject,
    mut v_i_4275_: *mut leanh::LeanObject,
    mut v_a_4276_: *mut leanh::LeanObject,
    mut v_x_4277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4278_ = leanh::lean_apply_2(v_f_4274_, v_i_4275_, v_a_4276_);
    return v___x_4278_;
}
pub unsafe fn l_Vector_mapIdx___redArg(
    mut v_f_4279_: *mut leanh::LeanObject,
    mut v_xs_4280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4281_ = leanh::lean_alloc_closure(
        l_Vector_mapIdx___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4281_, 0, v_f_4279_);
    v___x_4282_ = l_Vector_foldl___redArg___closed__9;
    v___x_4283_ = lean_array_get_size(v_xs_4280_);
    v___x_4284_ = leanh::lean_unsigned_to_nat(0);
    v___x_4285_ = lean_mk_empty_array_with_capacity(v___x_4283_);
    v___x_4286_ = l_Array_mapFinIdxM_map___redArg(
        v___x_4282_,
        v_xs_4280_,
        v___f_4281_,
        v___x_4283_,
        v___x_4284_,
        v___x_4285_,
    );
    return v___x_4286_;
}
pub unsafe fn l_Vector_mapIdx(
    mut v_00_u03b1_4287_: *mut leanh::LeanObject,
    mut v_00_u03b2_4288_: *mut leanh::LeanObject,
    mut v_n_4289_: *mut leanh::LeanObject,
    mut v_f_4290_: *mut leanh::LeanObject,
    mut v_xs_4291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4292_ = leanh::lean_alloc_closure(
        l_Vector_mapIdx___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4292_, 0, v_f_4290_);
    v___x_4293_ = l_Vector_foldl___redArg___closed__9;
    v___x_4294_ = lean_array_get_size(v_xs_4291_);
    v___x_4295_ = leanh::lean_unsigned_to_nat(0);
    v___x_4296_ = lean_mk_empty_array_with_capacity(v___x_4294_);
    v___x_4297_ = l_Array_mapFinIdxM_map___redArg(
        v___x_4293_,
        v_xs_4291_,
        v___f_4292_,
        v___x_4294_,
        v___x_4295_,
        v___x_4296_,
    );
    return v___x_4297_;
}
pub unsafe fn l_Vector_mapIdx___boxed(
    mut v_00_u03b1_4298_: *mut leanh::LeanObject,
    mut v_00_u03b2_4299_: *mut leanh::LeanObject,
    mut v_n_4300_: *mut leanh::LeanObject,
    mut v_f_4301_: *mut leanh::LeanObject,
    mut v_xs_4302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4303_ = l_Vector_mapIdx(
        v_00_u03b1_4298_,
        v_00_u03b2_4299_,
        v_n_4300_,
        v_f_4301_,
        v_xs_4302_,
    );
    leanh::lean_dec(v_n_4300_);
    return v_res_4303_;
}
pub unsafe fn l_Vector_mapFinIdx___redArg___lam__0(
    mut v_f_4304_: *mut leanh::LeanObject,
    mut v_x1_4305_: *mut leanh::LeanObject,
    mut v_x2_4306_: *mut leanh::LeanObject,
    mut v_x3_4307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4308_ =
        leanh::lean_apply_3(v_f_4304_, v_x1_4305_, v_x2_4306_, leanh::lean_box(0));
    return v___x_4308_;
}
pub unsafe fn l_Vector_mapFinIdx___redArg(
    mut v_xs_4309_: *mut leanh::LeanObject,
    mut v_f_4310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4311_ = leanh::lean_alloc_closure(
        l_Vector_mapFinIdx___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4311_, 0, v_f_4310_);
    v___x_4312_ = l_Vector_foldl___redArg___closed__9;
    v___x_4313_ = lean_array_get_size(v_xs_4309_);
    v___x_4314_ = leanh::lean_unsigned_to_nat(0);
    v___x_4315_ = lean_mk_empty_array_with_capacity(v___x_4313_);
    v___x_4316_ = l_Array_mapFinIdxM_map___redArg(
        v___x_4312_,
        v_xs_4309_,
        v___f_4311_,
        v___x_4313_,
        v___x_4314_,
        v___x_4315_,
    );
    return v___x_4316_;
}
pub unsafe fn l_Vector_mapFinIdx(
    mut v_00_u03b1_4317_: *mut leanh::LeanObject,
    mut v_n_4318_: *mut leanh::LeanObject,
    mut v_00_u03b2_4319_: *mut leanh::LeanObject,
    mut v_xs_4320_: *mut leanh::LeanObject,
    mut v_f_4321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4322_ = leanh::lean_alloc_closure(
        l_Vector_mapFinIdx___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4322_, 0, v_f_4321_);
    v___x_4323_ = l_Vector_foldl___redArg___closed__9;
    v___x_4324_ = lean_array_get_size(v_xs_4320_);
    v___x_4325_ = leanh::lean_unsigned_to_nat(0);
    v___x_4326_ = lean_mk_empty_array_with_capacity(v___x_4324_);
    v___x_4327_ = l_Array_mapFinIdxM_map___redArg(
        v___x_4323_,
        v_xs_4320_,
        v___f_4322_,
        v___x_4324_,
        v___x_4325_,
        v___x_4326_,
    );
    return v___x_4327_;
}
pub unsafe fn l_Vector_mapFinIdx___boxed(
    mut v_00_u03b1_4328_: *mut leanh::LeanObject,
    mut v_n_4329_: *mut leanh::LeanObject,
    mut v_00_u03b2_4330_: *mut leanh::LeanObject,
    mut v_xs_4331_: *mut leanh::LeanObject,
    mut v_f_4332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4333_ = l_Vector_mapFinIdx(
        v_00_u03b1_4328_,
        v_n_4329_,
        v_00_u03b2_4330_,
        v_xs_4331_,
        v_f_4332_,
    );
    leanh::lean_dec(v_n_4329_);
    return v_res_4333_;
}
pub unsafe fn l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed(
    mut v_k_4334_: *mut leanh::LeanObject,
    mut v_acc_4335_: *mut leanh::LeanObject,
    mut v_n_4336_: *mut leanh::LeanObject,
    mut v_inst_4337_: *mut leanh::LeanObject,
    mut v_f_4338_: *mut leanh::LeanObject,
    mut v_xs_4339_: *mut leanh::LeanObject,
    mut v_____do__lift_4340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4341_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(
        v_k_4334_,
        v_acc_4335_,
        v_n_4336_,
        v_inst_4337_,
        v_f_4338_,
        v_xs_4339_,
        v_____do__lift_4340_,
    );
    leanh::lean_dec(v_k_4334_);
    return v_res_4341_;
}
pub unsafe fn l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(
    mut v_n_4342_: *mut leanh::LeanObject,
    mut v_inst_4343_: *mut leanh::LeanObject,
    mut v_f_4344_: *mut leanh::LeanObject,
    mut v_xs_4345_: *mut leanh::LeanObject,
    mut v_k_4346_: *mut leanh::LeanObject,
    mut v_acc_4347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4348_: u8 = 0;
    v___x_4348_ = lean_nat_dec_lt(v_k_4346_, v_n_4342_);
    if v___x_4348_ == 0 {
        let mut v_toApplicative_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_k_4346_);
        leanh::lean_dec_ref(v_xs_4345_);
        leanh::lean_dec(v_f_4344_);
        leanh::lean_dec(v_n_4342_);
        v_toApplicative_4349_ = leanh::lean_ctor_get(v_inst_4343_, 0);
        leanh::lean_inc_ref(v_toApplicative_4349_);
        leanh::lean_dec_ref(v_inst_4343_);
        v_toPure_4350_ = leanh::lean_ctor_get(v_toApplicative_4349_, 1);
        leanh::lean_inc(v_toPure_4350_);
        leanh::lean_dec_ref(v_toApplicative_4349_);
        v___x_4351_ =
            leanh::lean_apply_2(v_toPure_4350_, leanh::lean_box(0), v_acc_4347_);
        return v___x_4351_;
    } else {
        let mut v_toBind_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_4352_ = leanh::lean_ctor_get(v_inst_4343_, 1);
        leanh::lean_inc(v_toBind_4352_);
        leanh::lean_inc_ref(v_xs_4345_);
        leanh::lean_inc(v_f_4344_);
        leanh::lean_inc(v_k_4346_);
        v___f_4353_ = leanh::lean_alloc_closure(
            l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            7,
            6,
        );
        leanh::lean_closure_set(v___f_4353_, 0, v_k_4346_);
        leanh::lean_closure_set(v___f_4353_, 1, v_acc_4347_);
        leanh::lean_closure_set(v___f_4353_, 2, v_n_4342_);
        leanh::lean_closure_set(v___f_4353_, 3, v_inst_4343_);
        leanh::lean_closure_set(v___f_4353_, 4, v_f_4344_);
        leanh::lean_closure_set(v___f_4353_, 5, v_xs_4345_);
        v___x_4354_ = lean_array_fget(v_xs_4345_, v_k_4346_);
        leanh::lean_dec(v_k_4346_);
        leanh::lean_dec_ref(v_xs_4345_);
        v___x_4355_ = leanh::lean_apply_1(v_f_4344_, v___x_4354_);
        v___x_4356_ = leanh::lean_apply_4(
            v_toBind_4352_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4355_,
            v___f_4353_,
        );
        return v___x_4356_;
    }
}
pub unsafe fn l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(
    mut v_k_4357_: *mut leanh::LeanObject,
    mut v_acc_4358_: *mut leanh::LeanObject,
    mut v_n_4359_: *mut leanh::LeanObject,
    mut v_inst_4360_: *mut leanh::LeanObject,
    mut v_f_4361_: *mut leanh::LeanObject,
    mut v_xs_4362_: *mut leanh::LeanObject,
    mut v_____do__lift_4363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4364_ = leanh::lean_unsigned_to_nat(1);
    v___x_4365_ = lean_nat_add(v_k_4357_, v___x_4364_);
    v___x_4366_ = lean_array_push(v_acc_4358_, v_____do__lift_4363_);
    v___x_4367_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(
        v_n_4359_,
        v_inst_4360_,
        v_f_4361_,
        v_xs_4362_,
        v___x_4365_,
        v___x_4366_,
    );
    return v___x_4367_;
}
pub unsafe fn l___private_Init_Data_Vector_Basic_0__Vector_mapM_go(
    mut v_m_4368_: *mut leanh::LeanObject,
    mut v_00_u03b1_4369_: *mut leanh::LeanObject,
    mut v_00_u03b2_4370_: *mut leanh::LeanObject,
    mut v_n_4371_: *mut leanh::LeanObject,
    mut v_inst_4372_: *mut leanh::LeanObject,
    mut v_f_4373_: *mut leanh::LeanObject,
    mut v_xs_4374_: *mut leanh::LeanObject,
    mut v_k_4375_: *mut leanh::LeanObject,
    mut v_h_4376_: *mut leanh::LeanObject,
    mut v_acc_4377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4378_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(
        v_n_4371_,
        v_inst_4372_,
        v_f_4373_,
        v_xs_4374_,
        v_k_4375_,
        v_acc_4377_,
    );
    return v___x_4378_;
}
pub unsafe fn l_Vector_mapM___redArg(
    mut v_n_4381_: *mut leanh::LeanObject,
    mut v_inst_4382_: *mut leanh::LeanObject,
    mut v_f_4383_: *mut leanh::LeanObject,
    mut v_xs_4384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4385_ = leanh::lean_unsigned_to_nat(0);
    v___x_4386_ = l_Vector_mapM___redArg___closed__0;
    v___x_4387_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(
        v_n_4381_,
        v_inst_4382_,
        v_f_4383_,
        v_xs_4384_,
        v___x_4385_,
        v___x_4386_,
    );
    return v___x_4387_;
}
pub unsafe fn l_Vector_mapM(
    mut v_m_4388_: *mut leanh::LeanObject,
    mut v_00_u03b1_4389_: *mut leanh::LeanObject,
    mut v_00_u03b2_4390_: *mut leanh::LeanObject,
    mut v_n_4391_: *mut leanh::LeanObject,
    mut v_inst_4392_: *mut leanh::LeanObject,
    mut v_f_4393_: *mut leanh::LeanObject,
    mut v_xs_4394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4395_ = leanh::lean_unsigned_to_nat(0);
    v___x_4396_ = l_Vector_mapM___redArg___closed__0;
    v___x_4397_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(
        v_n_4391_,
        v_inst_4392_,
        v_f_4393_,
        v_xs_4394_,
        v___x_4395_,
        v___x_4396_,
    );
    return v___x_4397_;
}
pub unsafe fn l_Vector_forM___redArg___lam__0(
    mut v_f_4398_: *mut leanh::LeanObject,
    mut v_x_4399_: *mut leanh::LeanObject,
    mut v___y_4400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4401_ = leanh::lean_apply_1(v_f_4398_, v___y_4400_);
    return v___x_4401_;
}
pub unsafe fn l_Vector_forM___redArg(
    mut v_inst_4402_: *mut leanh::LeanObject,
    mut v_xs_4403_: *mut leanh::LeanObject,
    mut v_f_4404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: u8 = 0;
    v___x_4405_ = leanh::lean_unsigned_to_nat(0);
    v___x_4406_ = lean_array_get_size(v_xs_4403_);
    v___x_4407_ = leanh::lean_box(0);
    v___x_4408_ = lean_nat_dec_lt(v___x_4405_, v___x_4406_);
    if v___x_4408_ == 0 {
        let mut v_toApplicative_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_4404_);
        leanh::lean_dec_ref(v_xs_4403_);
        v_toApplicative_4409_ = leanh::lean_ctor_get(v_inst_4402_, 0);
        leanh::lean_inc_ref(v_toApplicative_4409_);
        leanh::lean_dec_ref(v_inst_4402_);
        v_toPure_4410_ = leanh::lean_ctor_get(v_toApplicative_4409_, 1);
        leanh::lean_inc(v_toPure_4410_);
        leanh::lean_dec_ref(v_toApplicative_4409_);
        v___x_4411_ =
            leanh::lean_apply_2(v_toPure_4410_, leanh::lean_box(0), v___x_4407_);
        return v___x_4411_;
    } else {
        let mut v___f_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4413_: u8 = 0;
        v___f_4412_ = leanh::lean_alloc_closure(
            l_Vector_forM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_4412_, 0, v_f_4404_);
        v___x_4413_ = lean_nat_dec_le(v___x_4406_, v___x_4406_);
        if v___x_4413_ == 0 {
            if v___x_4408_ == 0 {
                let mut v_toApplicative_4414_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_4412_);
                leanh::lean_dec_ref(v_xs_4403_);
                v_toApplicative_4414_ = leanh::lean_ctor_get(v_inst_4402_, 0);
                leanh::lean_inc_ref(v_toApplicative_4414_);
                leanh::lean_dec_ref(v_inst_4402_);
                v_toPure_4415_ = leanh::lean_ctor_get(v_toApplicative_4414_, 1);
                leanh::lean_inc(v_toPure_4415_);
                leanh::lean_dec_ref(v_toApplicative_4414_);
                v___x_4416_ = leanh::lean_apply_2(
                    v_toPure_4415_,
                    leanh::lean_box(0),
                    v___x_4407_,
                );
                return v___x_4416_;
            } else {
                let mut v___x_4417_: usize = 0;
                let mut v___x_4418_: usize = 0;
                let mut v___x_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4417_ = 0usize;
                v___x_4418_ = lean_usize_of_nat(v___x_4406_);
                v___x_4419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_4402_,
                    v___f_4412_,
                    v_xs_4403_,
                    v___x_4417_,
                    v___x_4418_,
                    v___x_4407_,
                );
                return v___x_4419_;
            }
        } else {
            let mut v___x_4420_: usize = 0;
            let mut v___x_4421_: usize = 0;
            let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4420_ = 0usize;
            v___x_4421_ = lean_usize_of_nat(v___x_4406_);
            v___x_4422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_4402_,
                v___f_4412_,
                v_xs_4403_,
                v___x_4420_,
                v___x_4421_,
                v___x_4407_,
            );
            return v___x_4422_;
        }
    }
}
pub unsafe fn l_Vector_forM(
    mut v_m_4423_: *mut leanh::LeanObject,
    mut v_00_u03b1_4424_: *mut leanh::LeanObject,
    mut v_n_4425_: *mut leanh::LeanObject,
    mut v_inst_4426_: *mut leanh::LeanObject,
    mut v_xs_4427_: *mut leanh::LeanObject,
    mut v_f_4428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: u8 = 0;
    v___x_4429_ = leanh::lean_unsigned_to_nat(0);
    v___x_4430_ = lean_array_get_size(v_xs_4427_);
    v___x_4431_ = leanh::lean_box(0);
    v___x_4432_ = lean_nat_dec_lt(v___x_4429_, v___x_4430_);
    if v___x_4432_ == 0 {
        let mut v_toApplicative_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_4428_);
        leanh::lean_dec_ref(v_xs_4427_);
        v_toApplicative_4433_ = leanh::lean_ctor_get(v_inst_4426_, 0);
        leanh::lean_inc_ref(v_toApplicative_4433_);
        leanh::lean_dec_ref(v_inst_4426_);
        v_toPure_4434_ = leanh::lean_ctor_get(v_toApplicative_4433_, 1);
        leanh::lean_inc(v_toPure_4434_);
        leanh::lean_dec_ref(v_toApplicative_4433_);
        v___x_4435_ =
            leanh::lean_apply_2(v_toPure_4434_, leanh::lean_box(0), v___x_4431_);
        return v___x_4435_;
    } else {
        let mut v___f_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4437_: u8 = 0;
        v___f_4436_ = leanh::lean_alloc_closure(
            l_Vector_forM___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_4436_, 0, v_f_4428_);
        v___x_4437_ = lean_nat_dec_le(v___x_4430_, v___x_4430_);
        if v___x_4437_ == 0 {
            if v___x_4432_ == 0 {
                let mut v_toApplicative_4438_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___f_4436_);
                leanh::lean_dec_ref(v_xs_4427_);
                v_toApplicative_4438_ = leanh::lean_ctor_get(v_inst_4426_, 0);
                leanh::lean_inc_ref(v_toApplicative_4438_);
                leanh::lean_dec_ref(v_inst_4426_);
                v_toPure_4439_ = leanh::lean_ctor_get(v_toApplicative_4438_, 1);
                leanh::lean_inc(v_toPure_4439_);
                leanh::lean_dec_ref(v_toApplicative_4438_);
                v___x_4440_ = leanh::lean_apply_2(
                    v_toPure_4439_,
                    leanh::lean_box(0),
                    v___x_4431_,
                );
                return v___x_4440_;
            } else {
                let mut v___x_4441_: usize = 0;
                let mut v___x_4442_: usize = 0;
                let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4441_ = 0usize;
                v___x_4442_ = lean_usize_of_nat(v___x_4430_);
                v___x_4443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_4426_,
                    v___f_4436_,
                    v_xs_4427_,
                    v___x_4441_,
                    v___x_4442_,
                    v___x_4431_,
                );
                return v___x_4443_;
            }
        } else {
            let mut v___x_4444_: usize = 0;
            let mut v___x_4445_: usize = 0;
            let mut v___x_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4444_ = 0usize;
            v___x_4445_ = lean_usize_of_nat(v___x_4430_);
            v___x_4446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_4426_,
                v___f_4436_,
                v_xs_4427_,
                v___x_4444_,
                v___x_4445_,
                v___x_4431_,
            );
            return v___x_4446_;
        }
    }
}
pub unsafe fn l_Vector_forM___boxed(
    mut v_m_4447_: *mut leanh::LeanObject,
    mut v_00_u03b1_4448_: *mut leanh::LeanObject,
    mut v_n_4449_: *mut leanh::LeanObject,
    mut v_inst_4450_: *mut leanh::LeanObject,
    mut v_xs_4451_: *mut leanh::LeanObject,
    mut v_f_4452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4453_ = l_Vector_forM(
        v_m_4447_,
        v_00_u03b1_4448_,
        v_n_4449_,
        v_inst_4450_,
        v_xs_4451_,
        v_f_4452_,
    );
    leanh::lean_dec(v_n_4449_);
    return v_res_4453_;
}
pub unsafe fn l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed(
    mut v_i_4454_: *mut leanh::LeanObject,
    mut v_acc_4455_: *mut leanh::LeanObject,
    mut v_n_4456_: *mut leanh::LeanObject,
    mut v_inst_4457_: *mut leanh::LeanObject,
    mut v_xs_4458_: *mut leanh::LeanObject,
    mut v_f_4459_: *mut leanh::LeanObject,
    mut v_____do__lift_4460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4461_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(
        v_i_4454_,
        v_acc_4455_,
        v_n_4456_,
        v_inst_4457_,
        v_xs_4458_,
        v_f_4459_,
        v_____do__lift_4460_,
    );
    leanh::lean_dec_ref(v_____do__lift_4460_);
    leanh::lean_dec(v_i_4454_);
    return v_res_4461_;
}
pub unsafe fn l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(
    mut v_n_4462_: *mut leanh::LeanObject,
    mut v_inst_4463_: *mut leanh::LeanObject,
    mut v_xs_4464_: *mut leanh::LeanObject,
    mut v_f_4465_: *mut leanh::LeanObject,
    mut v_i_4466_: *mut leanh::LeanObject,
    mut v_acc_4467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4468_: u8 = 0;
    v___x_4468_ = lean_nat_dec_lt(v_i_4466_, v_n_4462_);
    if v___x_4468_ == 0 {
        let mut v_toApplicative_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_i_4466_);
        leanh::lean_dec(v_f_4465_);
        leanh::lean_dec_ref(v_xs_4464_);
        leanh::lean_dec(v_n_4462_);
        v_toApplicative_4469_ = leanh::lean_ctor_get(v_inst_4463_, 0);
        leanh::lean_inc_ref(v_toApplicative_4469_);
        leanh::lean_dec_ref(v_inst_4463_);
        v_toPure_4470_ = leanh::lean_ctor_get(v_toApplicative_4469_, 1);
        leanh::lean_inc(v_toPure_4470_);
        leanh::lean_dec_ref(v_toApplicative_4469_);
        v___x_4471_ =
            leanh::lean_apply_2(v_toPure_4470_, leanh::lean_box(0), v_acc_4467_);
        return v___x_4471_;
    } else {
        let mut v_toBind_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_4472_ = leanh::lean_ctor_get(v_inst_4463_, 1);
        leanh::lean_inc(v_toBind_4472_);
        leanh::lean_inc(v_f_4465_);
        leanh::lean_inc_ref(v_xs_4464_);
        leanh::lean_inc(v_i_4466_);
        v___f_4473_ = leanh::lean_alloc_closure(
            l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            7,
            6,
        );
        leanh::lean_closure_set(v___f_4473_, 0, v_i_4466_);
        leanh::lean_closure_set(v___f_4473_, 1, v_acc_4467_);
        leanh::lean_closure_set(v___f_4473_, 2, v_n_4462_);
        leanh::lean_closure_set(v___f_4473_, 3, v_inst_4463_);
        leanh::lean_closure_set(v___f_4473_, 4, v_xs_4464_);
        leanh::lean_closure_set(v___f_4473_, 5, v_f_4465_);
        v___x_4474_ = lean_array_fget(v_xs_4464_, v_i_4466_);
        leanh::lean_dec(v_i_4466_);
        leanh::lean_dec_ref(v_xs_4464_);
        v___x_4475_ = leanh::lean_apply_1(v_f_4465_, v___x_4474_);
        v___x_4476_ = leanh::lean_apply_4(
            v_toBind_4472_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4475_,
            v___f_4473_,
        );
        return v___x_4476_;
    }
}
pub unsafe fn l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(
    mut v_i_4477_: *mut leanh::LeanObject,
    mut v_acc_4478_: *mut leanh::LeanObject,
    mut v_n_4479_: *mut leanh::LeanObject,
    mut v_inst_4480_: *mut leanh::LeanObject,
    mut v_xs_4481_: *mut leanh::LeanObject,
    mut v_f_4482_: *mut leanh::LeanObject,
    mut v_____do__lift_4483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4484_ = leanh::lean_unsigned_to_nat(1);
    v___x_4485_ = lean_nat_add(v_i_4477_, v___x_4484_);
    v___x_4486_ = l_Array_append___redArg(v_acc_4478_, v_____do__lift_4483_);
    v___x_4487_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(
        v_n_4479_,
        v_inst_4480_,
        v_xs_4481_,
        v_f_4482_,
        v___x_4485_,
        v___x_4486_,
    );
    return v___x_4487_;
}
pub unsafe fn l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(
    mut v_m_4488_: *mut leanh::LeanObject,
    mut v_00_u03b1_4489_: *mut leanh::LeanObject,
    mut v_n_4490_: *mut leanh::LeanObject,
    mut v_00_u03b2_4491_: *mut leanh::LeanObject,
    mut v_k_4492_: *mut leanh::LeanObject,
    mut v_inst_4493_: *mut leanh::LeanObject,
    mut v_xs_4494_: *mut leanh::LeanObject,
    mut v_f_4495_: *mut leanh::LeanObject,
    mut v_i_4496_: *mut leanh::LeanObject,
    mut v_h_4497_: *mut leanh::LeanObject,
    mut v_acc_4498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4499_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(
        v_n_4490_,
        v_inst_4493_,
        v_xs_4494_,
        v_f_4495_,
        v_i_4496_,
        v_acc_4498_,
    );
    return v___x_4499_;
}
pub unsafe fn l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___boxed(
    mut v_m_4500_: *mut leanh::LeanObject,
    mut v_00_u03b1_4501_: *mut leanh::LeanObject,
    mut v_n_4502_: *mut leanh::LeanObject,
    mut v_00_u03b2_4503_: *mut leanh::LeanObject,
    mut v_k_4504_: *mut leanh::LeanObject,
    mut v_inst_4505_: *mut leanh::LeanObject,
    mut v_xs_4506_: *mut leanh::LeanObject,
    mut v_f_4507_: *mut leanh::LeanObject,
    mut v_i_4508_: *mut leanh::LeanObject,
    mut v_h_4509_: *mut leanh::LeanObject,
    mut v_acc_4510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4511_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(
        v_m_4500_,
        v_00_u03b1_4501_,
        v_n_4502_,
        v_00_u03b2_4503_,
        v_k_4504_,
        v_inst_4505_,
        v_xs_4506_,
        v_f_4507_,
        v_i_4508_,
        v_h_4509_,
        v_acc_4510_,
    );
    leanh::lean_dec(v_k_4504_);
    return v_res_4511_;
}
pub unsafe fn l_Vector_flatMapM___redArg(
    mut v_n_4512_: *mut leanh::LeanObject,
    mut v_inst_4513_: *mut leanh::LeanObject,
    mut v_xs_4514_: *mut leanh::LeanObject,
    mut v_f_4515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4516_ = leanh::lean_unsigned_to_nat(0);
    v___x_4517_ = l_Vector_mapM___redArg___closed__0;
    v___x_4518_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(
        v_n_4512_,
        v_inst_4513_,
        v_xs_4514_,
        v_f_4515_,
        v___x_4516_,
        v___x_4517_,
    );
    return v___x_4518_;
}
pub unsafe fn l_Vector_flatMapM(
    mut v_m_4519_: *mut leanh::LeanObject,
    mut v_00_u03b1_4520_: *mut leanh::LeanObject,
    mut v_n_4521_: *mut leanh::LeanObject,
    mut v_00_u03b2_4522_: *mut leanh::LeanObject,
    mut v_k_4523_: *mut leanh::LeanObject,
    mut v_inst_4524_: *mut leanh::LeanObject,
    mut v_xs_4525_: *mut leanh::LeanObject,
    mut v_f_4526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4527_ = leanh::lean_unsigned_to_nat(0);
    v___x_4528_ = l_Vector_mapM___redArg___closed__0;
    v___x_4529_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(
        v_n_4521_,
        v_inst_4524_,
        v_xs_4525_,
        v_f_4526_,
        v___x_4527_,
        v___x_4528_,
    );
    return v___x_4529_;
}
pub unsafe fn l_Vector_flatMapM___boxed(
    mut v_m_4530_: *mut leanh::LeanObject,
    mut v_00_u03b1_4531_: *mut leanh::LeanObject,
    mut v_n_4532_: *mut leanh::LeanObject,
    mut v_00_u03b2_4533_: *mut leanh::LeanObject,
    mut v_k_4534_: *mut leanh::LeanObject,
    mut v_inst_4535_: *mut leanh::LeanObject,
    mut v_xs_4536_: *mut leanh::LeanObject,
    mut v_f_4537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4538_ = l_Vector_flatMapM(
        v_m_4530_,
        v_00_u03b1_4531_,
        v_n_4532_,
        v_00_u03b2_4533_,
        v_k_4534_,
        v_inst_4535_,
        v_xs_4536_,
        v_f_4537_,
    );
    leanh::lean_dec(v_k_4534_);
    return v_res_4538_;
}
pub unsafe fn l_Vector_mapFinIdxM_map___redArg___lam__0___boxed(
    mut v_j_4539_: *mut leanh::LeanObject,
    mut v_ys_4540_: *mut leanh::LeanObject,
    mut v_inst_4541_: *mut leanh::LeanObject,
    mut v_xs_4542_: *mut leanh::LeanObject,
    mut v_f_4543_: *mut leanh::LeanObject,
    mut v_n_4544_: *mut leanh::LeanObject,
    mut v_____do__lift_4545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4546_ = l_Vector_mapFinIdxM_map___redArg___lam__0(
        v_j_4539_,
        v_ys_4540_,
        v_inst_4541_,
        v_xs_4542_,
        v_f_4543_,
        v_n_4544_,
        v_____do__lift_4545_,
    );
    leanh::lean_dec(v_n_4544_);
    leanh::lean_dec(v_j_4539_);
    return v_res_4546_;
}
pub unsafe fn l_Vector_mapFinIdxM_map___redArg(
    mut v_inst_4547_: *mut leanh::LeanObject,
    mut v_xs_4548_: *mut leanh::LeanObject,
    mut v_f_4549_: *mut leanh::LeanObject,
    mut v_i_4550_: *mut leanh::LeanObject,
    mut v_j_4551_: *mut leanh::LeanObject,
    mut v_ys_4552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4557_: u8 = 0;
    v_toApplicative_4553_ = leanh::lean_ctor_get(v_inst_4547_, 0);
    v_toBind_4554_ = leanh::lean_ctor_get(v_inst_4547_, 1);
    leanh::lean_inc(v_toBind_4554_);
    v_toPure_4555_ = leanh::lean_ctor_get(v_toApplicative_4553_, 1);
    v_zero_4556_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_4557_ = lean_nat_dec_eq(v_i_4550_, v_zero_4556_);
    if v_isZero_4557_ == 1 {
        let mut v___x_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_toPure_4555_);
        leanh::lean_dec(v_toBind_4554_);
        leanh::lean_dec(v_j_4551_);
        leanh::lean_dec(v_f_4549_);
        leanh::lean_dec_ref(v_xs_4548_);
        leanh::lean_dec_ref(v_inst_4547_);
        v___x_4558_ =
            leanh::lean_apply_2(v_toPure_4555_, leanh::lean_box(0), v_ys_4552_);
        return v___x_4558_;
    } else {
        let mut v_one_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_one_4559_ = leanh::lean_unsigned_to_nat(1);
        v_n_4560_ = lean_nat_sub(v_i_4550_, v_one_4559_);
        leanh::lean_inc(v_f_4549_);
        leanh::lean_inc_ref(v_xs_4548_);
        leanh::lean_inc(v_j_4551_);
        v___f_4561_ = leanh::lean_alloc_closure(
            l_Vector_mapFinIdxM_map___redArg___lam__0___boxed as *mut core::ffi::c_void,
            7,
            6,
        );
        leanh::lean_closure_set(v___f_4561_, 0, v_j_4551_);
        leanh::lean_closure_set(v___f_4561_, 1, v_ys_4552_);
        leanh::lean_closure_set(v___f_4561_, 2, v_inst_4547_);
        leanh::lean_closure_set(v___f_4561_, 3, v_xs_4548_);
        leanh::lean_closure_set(v___f_4561_, 4, v_f_4549_);
        leanh::lean_closure_set(v___f_4561_, 5, v_n_4560_);
        v___x_4562_ = lean_array_fget(v_xs_4548_, v_j_4551_);
        leanh::lean_dec_ref(v_xs_4548_);
        v___x_4563_ = leanh::lean_apply_3(
            v_f_4549_,
            v_j_4551_,
            v___x_4562_,
            leanh::lean_box(0),
        );
        v___x_4564_ = leanh::lean_apply_4(
            v_toBind_4554_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4563_,
            v___f_4561_,
        );
        return v___x_4564_;
    }
}
pub unsafe fn l_Vector_mapFinIdxM_map___redArg___lam__0(
    mut v_j_4565_: *mut leanh::LeanObject,
    mut v_ys_4566_: *mut leanh::LeanObject,
    mut v_inst_4567_: *mut leanh::LeanObject,
    mut v_xs_4568_: *mut leanh::LeanObject,
    mut v_f_4569_: *mut leanh::LeanObject,
    mut v_n_4570_: *mut leanh::LeanObject,
    mut v_____do__lift_4571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4572_ = leanh::lean_unsigned_to_nat(1);
    v___x_4573_ = lean_nat_add(v_j_4565_, v___x_4572_);
    v___x_4574_ = lean_array_push(v_ys_4566_, v_____do__lift_4571_);
    v___x_4575_ = l_Vector_mapFinIdxM_map___redArg(
        v_inst_4567_,
        v_xs_4568_,
        v_f_4569_,
        v_n_4570_,
        v___x_4573_,
        v___x_4574_,
    );
    return v___x_4575_;
}
pub unsafe fn l_Vector_mapFinIdxM_map___redArg___boxed(
    mut v_inst_4576_: *mut leanh::LeanObject,
    mut v_xs_4577_: *mut leanh::LeanObject,
    mut v_f_4578_: *mut leanh::LeanObject,
    mut v_i_4579_: *mut leanh::LeanObject,
    mut v_j_4580_: *mut leanh::LeanObject,
    mut v_ys_4581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4582_ = l_Vector_mapFinIdxM_map___redArg(
        v_inst_4576_,
        v_xs_4577_,
        v_f_4578_,
        v_i_4579_,
        v_j_4580_,
        v_ys_4581_,
    );
    leanh::lean_dec(v_i_4579_);
    return v_res_4582_;
}
pub unsafe fn l_Vector_mapFinIdxM_map(
    mut v_n_4583_: *mut leanh::LeanObject,
    mut v_00_u03b1_4584_: *mut leanh::LeanObject,
    mut v_00_u03b2_4585_: *mut leanh::LeanObject,
    mut v_m_4586_: *mut leanh::LeanObject,
    mut v_inst_4587_: *mut leanh::LeanObject,
    mut v_xs_4588_: *mut leanh::LeanObject,
    mut v_f_4589_: *mut leanh::LeanObject,
    mut v_i_4590_: *mut leanh::LeanObject,
    mut v_j_4591_: *mut leanh::LeanObject,
    mut v_inv_4592_: *mut leanh::LeanObject,
    mut v_ys_4593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4594_ = l_Vector_mapFinIdxM_map___redArg(
        v_inst_4587_,
        v_xs_4588_,
        v_f_4589_,
        v_i_4590_,
        v_j_4591_,
        v_ys_4593_,
    );
    return v___x_4594_;
}
pub unsafe fn l_Vector_mapFinIdxM_map___boxed(
    mut v_n_4595_: *mut leanh::LeanObject,
    mut v_00_u03b1_4596_: *mut leanh::LeanObject,
    mut v_00_u03b2_4597_: *mut leanh::LeanObject,
    mut v_m_4598_: *mut leanh::LeanObject,
    mut v_inst_4599_: *mut leanh::LeanObject,
    mut v_xs_4600_: *mut leanh::LeanObject,
    mut v_f_4601_: *mut leanh::LeanObject,
    mut v_i_4602_: *mut leanh::LeanObject,
    mut v_j_4603_: *mut leanh::LeanObject,
    mut v_inv_4604_: *mut leanh::LeanObject,
    mut v_ys_4605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4606_ = l_Vector_mapFinIdxM_map(
        v_n_4595_,
        v_00_u03b1_4596_,
        v_00_u03b2_4597_,
        v_m_4598_,
        v_inst_4599_,
        v_xs_4600_,
        v_f_4601_,
        v_i_4602_,
        v_j_4603_,
        v_inv_4604_,
        v_ys_4605_,
    );
    leanh::lean_dec(v_i_4602_);
    leanh::lean_dec(v_n_4595_);
    return v_res_4606_;
}
pub unsafe fn l_Vector_mapFinIdxM___redArg(
    mut v_n_4607_: *mut leanh::LeanObject,
    mut v_inst_4608_: *mut leanh::LeanObject,
    mut v_xs_4609_: *mut leanh::LeanObject,
    mut v_f_4610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4611_ = leanh::lean_unsigned_to_nat(0);
    v___x_4612_ = l_Vector_mapM___redArg___closed__0;
    v___x_4613_ = l_Vector_mapFinIdxM_map___redArg(
        v_inst_4608_,
        v_xs_4609_,
        v_f_4610_,
        v_n_4607_,
        v___x_4611_,
        v___x_4612_,
    );
    return v___x_4613_;
}
pub unsafe fn l_Vector_mapFinIdxM___redArg___boxed(
    mut v_n_4614_: *mut leanh::LeanObject,
    mut v_inst_4615_: *mut leanh::LeanObject,
    mut v_xs_4616_: *mut leanh::LeanObject,
    mut v_f_4617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4618_ = l_Vector_mapFinIdxM___redArg(v_n_4614_, v_inst_4615_, v_xs_4616_, v_f_4617_);
    leanh::lean_dec(v_n_4614_);
    return v_res_4618_;
}
pub unsafe fn l_Vector_mapFinIdxM(
    mut v_n_4619_: *mut leanh::LeanObject,
    mut v_00_u03b1_4620_: *mut leanh::LeanObject,
    mut v_00_u03b2_4621_: *mut leanh::LeanObject,
    mut v_m_4622_: *mut leanh::LeanObject,
    mut v_inst_4623_: *mut leanh::LeanObject,
    mut v_xs_4624_: *mut leanh::LeanObject,
    mut v_f_4625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4626_ = leanh::lean_unsigned_to_nat(0);
    v___x_4627_ = l_Vector_mapM___redArg___closed__0;
    v___x_4628_ = l_Vector_mapFinIdxM_map___redArg(
        v_inst_4623_,
        v_xs_4624_,
        v_f_4625_,
        v_n_4619_,
        v___x_4626_,
        v___x_4627_,
    );
    return v___x_4628_;
}
pub unsafe fn l_Vector_mapFinIdxM___boxed(
    mut v_n_4629_: *mut leanh::LeanObject,
    mut v_00_u03b1_4630_: *mut leanh::LeanObject,
    mut v_00_u03b2_4631_: *mut leanh::LeanObject,
    mut v_m_4632_: *mut leanh::LeanObject,
    mut v_inst_4633_: *mut leanh::LeanObject,
    mut v_xs_4634_: *mut leanh::LeanObject,
    mut v_f_4635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4636_ = l_Vector_mapFinIdxM(
        v_n_4629_,
        v_00_u03b1_4630_,
        v_00_u03b2_4631_,
        v_m_4632_,
        v_inst_4633_,
        v_xs_4634_,
        v_f_4635_,
    );
    leanh::lean_dec(v_n_4629_);
    return v_res_4636_;
}
pub unsafe fn l_Vector_mapIdxM___redArg(
    mut v_n_4637_: *mut leanh::LeanObject,
    mut v_inst_4638_: *mut leanh::LeanObject,
    mut v_f_4639_: *mut leanh::LeanObject,
    mut v_xs_4640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4641_ = leanh::lean_alloc_closure(
        l_Vector_mapIdx___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4641_, 0, v_f_4639_);
    v___x_4642_ = leanh::lean_unsigned_to_nat(0);
    v___x_4643_ = l_Vector_mapM___redArg___closed__0;
    v___x_4644_ = l_Vector_mapFinIdxM_map___redArg(
        v_inst_4638_,
        v_xs_4640_,
        v___f_4641_,
        v_n_4637_,
        v___x_4642_,
        v___x_4643_,
    );
    return v___x_4644_;
}
pub unsafe fn l_Vector_mapIdxM___redArg___boxed(
    mut v_n_4645_: *mut leanh::LeanObject,
    mut v_inst_4646_: *mut leanh::LeanObject,
    mut v_f_4647_: *mut leanh::LeanObject,
    mut v_xs_4648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4649_ = l_Vector_mapIdxM___redArg(v_n_4645_, v_inst_4646_, v_f_4647_, v_xs_4648_);
    leanh::lean_dec(v_n_4645_);
    return v_res_4649_;
}
pub unsafe fn l_Vector_mapIdxM(
    mut v_n_4650_: *mut leanh::LeanObject,
    mut v_00_u03b1_4651_: *mut leanh::LeanObject,
    mut v_00_u03b2_4652_: *mut leanh::LeanObject,
    mut v_m_4653_: *mut leanh::LeanObject,
    mut v_inst_4654_: *mut leanh::LeanObject,
    mut v_f_4655_: *mut leanh::LeanObject,
    mut v_xs_4656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4657_ = leanh::lean_alloc_closure(
        l_Vector_mapIdx___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_4657_, 0, v_f_4655_);
    v___x_4658_ = leanh::lean_unsigned_to_nat(0);
    v___x_4659_ = l_Vector_mapM___redArg___closed__0;
    v___x_4660_ = l_Vector_mapFinIdxM_map___redArg(
        v_inst_4654_,
        v_xs_4656_,
        v___f_4657_,
        v_n_4650_,
        v___x_4658_,
        v___x_4659_,
    );
    return v___x_4660_;
}
pub unsafe fn l_Vector_mapIdxM___boxed(
    mut v_n_4661_: *mut leanh::LeanObject,
    mut v_00_u03b1_4662_: *mut leanh::LeanObject,
    mut v_00_u03b2_4663_: *mut leanh::LeanObject,
    mut v_m_4664_: *mut leanh::LeanObject,
    mut v_inst_4665_: *mut leanh::LeanObject,
    mut v_f_4666_: *mut leanh::LeanObject,
    mut v_xs_4667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4668_ = l_Vector_mapIdxM(
        v_n_4661_,
        v_00_u03b1_4662_,
        v_00_u03b2_4663_,
        v_m_4664_,
        v_inst_4665_,
        v_f_4666_,
        v_xs_4667_,
    );
    leanh::lean_dec(v_n_4661_);
    return v_res_4668_;
}
pub unsafe fn l_Vector_firstM___redArg(
    mut v_inst_4669_: *mut leanh::LeanObject,
    mut v_f_4670_: *mut leanh::LeanObject,
    mut v_xs_4671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4672_ = leanh::lean_unsigned_to_nat(0);
    v___x_4673_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_4669_,
        v_f_4670_,
        v_xs_4671_,
        v___x_4672_,
    );
    return v___x_4673_;
}
pub unsafe fn l_Vector_firstM(
    mut v_00_u03b2_4674_: *mut leanh::LeanObject,
    mut v_n_4675_: *mut leanh::LeanObject,
    mut v_00_u03b1_4676_: *mut leanh::LeanObject,
    mut v_m_4677_: *mut leanh::LeanObject,
    mut v_inst_4678_: *mut leanh::LeanObject,
    mut v_f_4679_: *mut leanh::LeanObject,
    mut v_xs_4680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4681_ = leanh::lean_unsigned_to_nat(0);
    v___x_4682_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_4678_,
        v_f_4679_,
        v_xs_4680_,
        v___x_4681_,
    );
    return v___x_4682_;
}
pub unsafe fn l_Vector_firstM___boxed(
    mut v_00_u03b2_4683_: *mut leanh::LeanObject,
    mut v_n_4684_: *mut leanh::LeanObject,
    mut v_00_u03b1_4685_: *mut leanh::LeanObject,
    mut v_m_4686_: *mut leanh::LeanObject,
    mut v_inst_4687_: *mut leanh::LeanObject,
    mut v_f_4688_: *mut leanh::LeanObject,
    mut v_xs_4689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4690_ = l_Vector_firstM(
        v_00_u03b2_4683_,
        v_n_4684_,
        v_00_u03b1_4685_,
        v_m_4686_,
        v_inst_4687_,
        v_f_4688_,
        v_xs_4689_,
    );
    leanh::lean_dec(v_n_4684_);
    return v_res_4690_;
}
pub unsafe fn l_Vector_flatten___redArg___lam__0(
    mut v_x_4691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_x_4691_);
    return v_x_4691_;
}
pub unsafe fn l_Vector_flatten___redArg___lam__0___boxed(
    mut v_x_4692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4693_ = l_Vector_flatten___redArg___lam__0(v_x_4692_);
    leanh::lean_dec_ref(v_x_4692_);
    return v_res_4693_;
}
pub unsafe fn l_Vector_flatten___redArg(
    mut v_xs_4698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4701_: usize = 0;
    let mut v___x_4702_: usize = 0;
    let mut v___x_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: u8 = 0;
    v___f_4699_ = l_Vector_flatten___redArg___closed__0;
    v___x_4700_ = l_Vector_foldl___redArg___closed__9;
    v_sz_4701_ = lean_array_size(v_xs_4698_);
    v___x_4702_ = 0usize;
    v___x_4703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4700_,
        v___f_4699_,
        v_sz_4701_,
        v___x_4702_,
        v_xs_4698_,
    );
    v___x_4704_ = leanh::lean_unsigned_to_nat(0);
    v___x_4705_ = l_Vector_flatten___redArg___closed__1;
    v___x_4706_ = lean_array_get_size(v___x_4703_);
    v___x_4707_ = lean_nat_dec_lt(v___x_4704_, v___x_4706_);
    if v___x_4707_ == 0 {
        leanh::lean_dec(v___x_4703_);
        return v___x_4705_;
    } else {
        let mut v___f_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4709_: u8 = 0;
        v___f_4708_ = l_Vector_flatten___redArg___closed__2;
        v___x_4709_ = lean_nat_dec_le(v___x_4706_, v___x_4706_);
        if v___x_4709_ == 0 {
            if v___x_4707_ == 0 {
                leanh::lean_dec(v___x_4703_);
                return v___x_4705_;
            } else {
                let mut v___x_4710_: usize = 0;
                let mut v___x_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4710_ = lean_usize_of_nat(v___x_4706_);
                v___x_4711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_4700_,
                    v___f_4708_,
                    v___x_4703_,
                    v___x_4702_,
                    v___x_4710_,
                    v___x_4705_,
                );
                return v___x_4711_;
            }
        } else {
            let mut v___x_4712_: usize = 0;
            let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4712_ = lean_usize_of_nat(v___x_4706_);
            v___x_4713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_4700_,
                v___f_4708_,
                v___x_4703_,
                v___x_4702_,
                v___x_4712_,
                v___x_4705_,
            );
            return v___x_4713_;
        }
    }
}
pub unsafe fn l_Vector_flatten(
    mut v_00_u03b1_4714_: *mut leanh::LeanObject,
    mut v_n_4715_: *mut leanh::LeanObject,
    mut v_m_4716_: *mut leanh::LeanObject,
    mut v_xs_4717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4720_: usize = 0;
    let mut v___x_4721_: usize = 0;
    let mut v___x_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: u8 = 0;
    v___f_4718_ = l_Vector_flatten___redArg___closed__0;
    v___x_4719_ = l_Vector_foldl___redArg___closed__9;
    v_sz_4720_ = lean_array_size(v_xs_4717_);
    v___x_4721_ = 0usize;
    v___x_4722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4719_,
        v___f_4718_,
        v_sz_4720_,
        v___x_4721_,
        v_xs_4717_,
    );
    v___x_4723_ = leanh::lean_unsigned_to_nat(0);
    v___x_4724_ = l_Vector_flatten___redArg___closed__1;
    v___x_4725_ = lean_array_get_size(v___x_4722_);
    v___x_4726_ = lean_nat_dec_lt(v___x_4723_, v___x_4725_);
    if v___x_4726_ == 0 {
        leanh::lean_dec(v___x_4722_);
        return v___x_4724_;
    } else {
        let mut v___f_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4728_: u8 = 0;
        v___f_4727_ = l_Vector_flatten___redArg___closed__2;
        v___x_4728_ = lean_nat_dec_le(v___x_4725_, v___x_4725_);
        if v___x_4728_ == 0 {
            if v___x_4726_ == 0 {
                leanh::lean_dec(v___x_4722_);
                return v___x_4724_;
            } else {
                let mut v___x_4729_: usize = 0;
                let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4729_ = lean_usize_of_nat(v___x_4725_);
                v___x_4730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_4719_,
                    v___f_4727_,
                    v___x_4722_,
                    v___x_4721_,
                    v___x_4729_,
                    v___x_4724_,
                );
                return v___x_4730_;
            }
        } else {
            let mut v___x_4731_: usize = 0;
            let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4731_ = lean_usize_of_nat(v___x_4725_);
            v___x_4732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_4719_,
                v___f_4727_,
                v___x_4722_,
                v___x_4721_,
                v___x_4731_,
                v___x_4724_,
            );
            return v___x_4732_;
        }
    }
}
pub unsafe fn l_Vector_flatten___boxed(
    mut v_00_u03b1_4733_: *mut leanh::LeanObject,
    mut v_n_4734_: *mut leanh::LeanObject,
    mut v_m_4735_: *mut leanh::LeanObject,
    mut v_xs_4736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4737_ = l_Vector_flatten(v_00_u03b1_4733_, v_n_4734_, v_m_4735_, v_xs_4736_);
    leanh::lean_dec(v_m_4735_);
    leanh::lean_dec(v_n_4734_);
    return v_res_4737_;
}
pub unsafe fn l_Vector_flatMap___redArg___lam__0(
    mut v_f_4738_: *mut leanh::LeanObject,
    mut v_x1_4739_: *mut leanh::LeanObject,
    mut v_x2_4740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4741_ = leanh::lean_apply_1(v_f_4738_, v_x2_4740_);
    v___x_4742_ = l_Array_append___redArg(v_x1_4739_, v___x_4741_);
    leanh::lean_dec_ref(v___x_4741_);
    return v___x_4742_;
}
pub unsafe fn l_Vector_flatMap___redArg(
    mut v_xs_4743_: *mut leanh::LeanObject,
    mut v_f_4744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: u8 = 0;
    v___x_4745_ = leanh::lean_unsigned_to_nat(0);
    v___x_4746_ = l_Vector_flatten___redArg___closed__1;
    v___x_4747_ = lean_array_get_size(v_xs_4743_);
    v___x_4748_ = l_Vector_foldl___redArg___closed__9;
    v___x_4749_ = lean_nat_dec_lt(v___x_4745_, v___x_4747_);
    if v___x_4749_ == 0 {
        leanh::lean_dec_ref(v_f_4744_);
        leanh::lean_dec_ref(v_xs_4743_);
        return v___x_4746_;
    } else {
        let mut v___f_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4751_: u8 = 0;
        v___f_4750_ = leanh::lean_alloc_closure(
            l_Vector_flatMap___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_4750_, 0, v_f_4744_);
        v___x_4751_ = lean_nat_dec_le(v___x_4747_, v___x_4747_);
        if v___x_4751_ == 0 {
            if v___x_4749_ == 0 {
                leanh::lean_dec_ref(v___f_4750_);
                leanh::lean_dec_ref(v_xs_4743_);
                return v___x_4746_;
            } else {
                let mut v___x_4752_: usize = 0;
                let mut v___x_4753_: usize = 0;
                let mut v___x_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4752_ = 0usize;
                v___x_4753_ = lean_usize_of_nat(v___x_4747_);
                v___x_4754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_4748_,
                    v___f_4750_,
                    v_xs_4743_,
                    v___x_4752_,
                    v___x_4753_,
                    v___x_4746_,
                );
                return v___x_4754_;
            }
        } else {
            let mut v___x_4755_: usize = 0;
            let mut v___x_4756_: usize = 0;
            let mut v___x_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4755_ = 0usize;
            v___x_4756_ = lean_usize_of_nat(v___x_4747_);
            v___x_4757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_4748_,
                v___f_4750_,
                v_xs_4743_,
                v___x_4755_,
                v___x_4756_,
                v___x_4746_,
            );
            return v___x_4757_;
        }
    }
}
pub unsafe fn l_Vector_flatMap(
    mut v_00_u03b1_4758_: *mut leanh::LeanObject,
    mut v_n_4759_: *mut leanh::LeanObject,
    mut v_00_u03b2_4760_: *mut leanh::LeanObject,
    mut v_m_4761_: *mut leanh::LeanObject,
    mut v_xs_4762_: *mut leanh::LeanObject,
    mut v_f_4763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: u8 = 0;
    v___x_4764_ = leanh::lean_unsigned_to_nat(0);
    v___x_4765_ = l_Vector_flatten___redArg___closed__1;
    v___x_4766_ = lean_array_get_size(v_xs_4762_);
    v___x_4767_ = l_Vector_foldl___redArg___closed__9;
    v___x_4768_ = lean_nat_dec_lt(v___x_4764_, v___x_4766_);
    if v___x_4768_ == 0 {
        leanh::lean_dec_ref(v_f_4763_);
        leanh::lean_dec_ref(v_xs_4762_);
        return v___x_4765_;
    } else {
        let mut v___f_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4770_: u8 = 0;
        v___f_4769_ = leanh::lean_alloc_closure(
            l_Vector_flatMap___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_4769_, 0, v_f_4763_);
        v___x_4770_ = lean_nat_dec_le(v___x_4766_, v___x_4766_);
        if v___x_4770_ == 0 {
            if v___x_4768_ == 0 {
                leanh::lean_dec_ref(v___f_4769_);
                leanh::lean_dec_ref(v_xs_4762_);
                return v___x_4765_;
            } else {
                let mut v___x_4771_: usize = 0;
                let mut v___x_4772_: usize = 0;
                let mut v___x_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4771_ = 0usize;
                v___x_4772_ = lean_usize_of_nat(v___x_4766_);
                v___x_4773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_4767_,
                    v___f_4769_,
                    v_xs_4762_,
                    v___x_4771_,
                    v___x_4772_,
                    v___x_4765_,
                );
                return v___x_4773_;
            }
        } else {
            let mut v___x_4774_: usize = 0;
            let mut v___x_4775_: usize = 0;
            let mut v___x_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4774_ = 0usize;
            v___x_4775_ = lean_usize_of_nat(v___x_4766_);
            v___x_4776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_4767_,
                v___f_4769_,
                v_xs_4762_,
                v___x_4774_,
                v___x_4775_,
                v___x_4765_,
            );
            return v___x_4776_;
        }
    }
}
pub unsafe fn l_Vector_flatMap___boxed(
    mut v_00_u03b1_4777_: *mut leanh::LeanObject,
    mut v_n_4778_: *mut leanh::LeanObject,
    mut v_00_u03b2_4779_: *mut leanh::LeanObject,
    mut v_m_4780_: *mut leanh::LeanObject,
    mut v_xs_4781_: *mut leanh::LeanObject,
    mut v_f_4782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4783_ = l_Vector_flatMap(
        v_00_u03b1_4777_,
        v_n_4778_,
        v_00_u03b2_4779_,
        v_m_4780_,
        v_xs_4781_,
        v_f_4782_,
    );
    leanh::lean_dec(v_m_4780_);
    leanh::lean_dec(v_n_4778_);
    return v_res_4783_;
}
pub unsafe fn l_Vector_zipIdx___redArg(
    mut v_xs_4784_: *mut leanh::LeanObject,
    mut v_k_4785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4786_ = l_Array_zipIdx___redArg(v_xs_4784_, v_k_4785_);
    return v___x_4786_;
}
pub unsafe fn l_Vector_zipIdx___redArg___boxed(
    mut v_xs_4787_: *mut leanh::LeanObject,
    mut v_k_4788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4789_ = l_Vector_zipIdx___redArg(v_xs_4787_, v_k_4788_);
    leanh::lean_dec(v_k_4788_);
    leanh::lean_dec_ref(v_xs_4787_);
    return v_res_4789_;
}
pub unsafe fn l_Vector_zipIdx(
    mut v_00_u03b1_4790_: *mut leanh::LeanObject,
    mut v_n_4791_: *mut leanh::LeanObject,
    mut v_xs_4792_: *mut leanh::LeanObject,
    mut v_k_4793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4794_ = l_Array_zipIdx___redArg(v_xs_4792_, v_k_4793_);
    return v___x_4794_;
}
pub unsafe fn l_Vector_zipIdx___boxed(
    mut v_00_u03b1_4795_: *mut leanh::LeanObject,
    mut v_n_4796_: *mut leanh::LeanObject,
    mut v_xs_4797_: *mut leanh::LeanObject,
    mut v_k_4798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4799_ = l_Vector_zipIdx(v_00_u03b1_4795_, v_n_4796_, v_xs_4797_, v_k_4798_);
    leanh::lean_dec(v_k_4798_);
    leanh::lean_dec_ref(v_xs_4797_);
    leanh::lean_dec(v_n_4796_);
    return v_res_4799_;
}
pub unsafe fn l_Vector_zip___redArg(
    mut v_as_4800_: *mut leanh::LeanObject,
    mut v_bs_4801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4802_ = l_Array_zip___redArg(v_as_4800_, v_bs_4801_);
    return v___x_4802_;
}
pub unsafe fn l_Vector_zip___redArg___boxed(
    mut v_as_4803_: *mut leanh::LeanObject,
    mut v_bs_4804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4805_ = l_Vector_zip___redArg(v_as_4803_, v_bs_4804_);
    leanh::lean_dec_ref(v_bs_4804_);
    leanh::lean_dec_ref(v_as_4803_);
    return v_res_4805_;
}
pub unsafe fn l_Vector_zip(
    mut v_00_u03b1_4806_: *mut leanh::LeanObject,
    mut v_n_4807_: *mut leanh::LeanObject,
    mut v_00_u03b2_4808_: *mut leanh::LeanObject,
    mut v_as_4809_: *mut leanh::LeanObject,
    mut v_bs_4810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4811_ = l_Array_zip___redArg(v_as_4809_, v_bs_4810_);
    return v___x_4811_;
}
pub unsafe fn l_Vector_zip___boxed(
    mut v_00_u03b1_4812_: *mut leanh::LeanObject,
    mut v_n_4813_: *mut leanh::LeanObject,
    mut v_00_u03b2_4814_: *mut leanh::LeanObject,
    mut v_as_4815_: *mut leanh::LeanObject,
    mut v_bs_4816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4817_ = l_Vector_zip(
        v_00_u03b1_4812_,
        v_n_4813_,
        v_00_u03b2_4814_,
        v_as_4815_,
        v_bs_4816_,
    );
    leanh::lean_dec_ref(v_bs_4816_);
    leanh::lean_dec_ref(v_as_4815_);
    leanh::lean_dec(v_n_4813_);
    return v_res_4817_;
}
pub unsafe fn l_Vector_zipWith___redArg(
    mut v_f_4818_: *mut leanh::LeanObject,
    mut v_as_4819_: *mut leanh::LeanObject,
    mut v_bs_4820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4821_ = leanh::lean_alloc_closure(
        l_Vector_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_4821_, 0, v_f_4818_);
    v___x_4822_ = l_Vector_foldl___redArg___closed__9;
    v___x_4823_ = leanh::lean_unsigned_to_nat(0);
    v___x_4824_ = l_Vector_mapM___redArg___closed__0;
    v___x_4825_ = l_Array_zipWithMAux___redArg(
        v___x_4822_,
        v_as_4819_,
        v_bs_4820_,
        v___f_4821_,
        v___x_4823_,
        v___x_4824_,
    );
    return v___x_4825_;
}
pub unsafe fn l_Vector_zipWith(
    mut v_00_u03b1_4826_: *mut leanh::LeanObject,
    mut v_00_u03b2_4827_: *mut leanh::LeanObject,
    mut v_00_u03c6_4828_: *mut leanh::LeanObject,
    mut v_n_4829_: *mut leanh::LeanObject,
    mut v_f_4830_: *mut leanh::LeanObject,
    mut v_as_4831_: *mut leanh::LeanObject,
    mut v_bs_4832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4833_ = leanh::lean_alloc_closure(
        l_Vector_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_4833_, 0, v_f_4830_);
    v___x_4834_ = l_Vector_foldl___redArg___closed__9;
    v___x_4835_ = leanh::lean_unsigned_to_nat(0);
    v___x_4836_ = l_Vector_mapM___redArg___closed__0;
    v___x_4837_ = l_Array_zipWithMAux___redArg(
        v___x_4834_,
        v_as_4831_,
        v_bs_4832_,
        v___f_4833_,
        v___x_4835_,
        v___x_4836_,
    );
    return v___x_4837_;
}
pub unsafe fn l_Vector_zipWith___boxed(
    mut v_00_u03b1_4838_: *mut leanh::LeanObject,
    mut v_00_u03b2_4839_: *mut leanh::LeanObject,
    mut v_00_u03c6_4840_: *mut leanh::LeanObject,
    mut v_n_4841_: *mut leanh::LeanObject,
    mut v_f_4842_: *mut leanh::LeanObject,
    mut v_as_4843_: *mut leanh::LeanObject,
    mut v_bs_4844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4845_ = l_Vector_zipWith(
        v_00_u03b1_4838_,
        v_00_u03b2_4839_,
        v_00_u03c6_4840_,
        v_n_4841_,
        v_f_4842_,
        v_as_4843_,
        v_bs_4844_,
    );
    leanh::lean_dec(v_n_4841_);
    return v_res_4845_;
}
pub unsafe fn l_Vector_unzip___redArg(
    mut v_xs_4846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4852_: u8 = 0;
    let mut v___x_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4856_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4847_ = l_Array_unzip___redArg(v_xs_4846_);
                v_fst_4848_ = leanh::lean_ctor_get(v___x_4847_, 0);
                v_snd_4849_ = leanh::lean_ctor_get(v___x_4847_, 1);
                v_isSharedCheck_4856_ = (!leanh::lean_is_exclusive(v___x_4847_)) as u8;
                if v_isSharedCheck_4856_ == 0 {
                    v___x_4851_ = v___x_4847_;
                    v_isShared_4852_ = v_isSharedCheck_4856_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4849_);
                    leanh::lean_inc(v_fst_4848_);
                    leanh::lean_dec(v___x_4847_);
                    v___x_4851_ = leanh::lean_box(0);
                    v_isShared_4852_ = v_isSharedCheck_4856_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4852_ == 0 {
                    v___x_4854_ = v___x_4851_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4855_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4855_, 0, v_fst_4848_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4855_, 1, v_snd_4849_);
                    v___x_4854_ = v_reuseFailAlloc_4855_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4854_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Vector_unzip___redArg___boxed(
    mut v_xs_4857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4858_ = l_Vector_unzip___redArg(v_xs_4857_);
    leanh::lean_dec_ref(v_xs_4857_);
    return v_res_4858_;
}
pub unsafe fn l_Vector_unzip(
    mut v_00_u03b1_4859_: *mut leanh::LeanObject,
    mut v_00_u03b2_4860_: *mut leanh::LeanObject,
    mut v_n_4861_: *mut leanh::LeanObject,
    mut v_xs_4862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4868_: u8 = 0;
    let mut v___x_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4872_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4863_ = l_Array_unzip___redArg(v_xs_4862_);
                v_fst_4864_ = leanh::lean_ctor_get(v___x_4863_, 0);
                v_snd_4865_ = leanh::lean_ctor_get(v___x_4863_, 1);
                v_isSharedCheck_4872_ = (!leanh::lean_is_exclusive(v___x_4863_)) as u8;
                if v_isSharedCheck_4872_ == 0 {
                    v___x_4867_ = v___x_4863_;
                    v_isShared_4868_ = v_isSharedCheck_4872_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4865_);
                    leanh::lean_inc(v_fst_4864_);
                    leanh::lean_dec(v___x_4863_);
                    v___x_4867_ = leanh::lean_box(0);
                    v_isShared_4868_ = v_isSharedCheck_4872_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4868_ == 0 {
                    v___x_4870_ = v___x_4867_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4871_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_fst_4864_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4871_, 1, v_snd_4865_);
                    v___x_4870_ = v_reuseFailAlloc_4871_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4870_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Vector_unzip___boxed(
    mut v_00_u03b1_4873_: *mut leanh::LeanObject,
    mut v_00_u03b2_4874_: *mut leanh::LeanObject,
    mut v_n_4875_: *mut leanh::LeanObject,
    mut v_xs_4876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4877_ = l_Vector_unzip(v_00_u03b1_4873_, v_00_u03b2_4874_, v_n_4875_, v_xs_4876_);
    leanh::lean_dec_ref(v_xs_4876_);
    leanh::lean_dec(v_n_4875_);
    return v_res_4877_;
}
pub unsafe fn l_Vector_ofFn___redArg(
    mut v_n_4878_: *mut leanh::LeanObject,
    mut v_f_4879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4880_ = l_Array_ofFn___redArg(v_n_4878_, v_f_4879_);
    return v___x_4880_;
}
pub unsafe fn l_Vector_ofFn(
    mut v_n_4881_: *mut leanh::LeanObject,
    mut v_00_u03b1_4882_: *mut leanh::LeanObject,
    mut v_f_4883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4884_ = l_Array_ofFn___redArg(v_n_4881_, v_f_4883_);
    return v___x_4884_;
}
pub unsafe fn _init_l_Vector_swap___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4885_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__17_once),
        _init_l_Vector_set___auto__1___closed__17,
    );
    return v___x_4885_;
}
pub unsafe fn _init_l_Vector_swap___auto__3() -> *mut leanh::LeanObject {
    let mut v___x_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4886_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__17_once),
        _init_l_Vector_set___auto__1___closed__17,
    );
    return v___x_4886_;
}
pub unsafe fn l_Vector_swap___redArg(
    mut v_xs_4887_: *mut leanh::LeanObject,
    mut v_i_4888_: *mut leanh::LeanObject,
    mut v_j_4889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4890_ = lean_array_fswap(v_xs_4887_, v_i_4888_, v_j_4889_);
    return v___x_4890_;
}
pub unsafe fn l_Vector_swap___redArg___boxed(
    mut v_xs_4891_: *mut leanh::LeanObject,
    mut v_i_4892_: *mut leanh::LeanObject,
    mut v_j_4893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4894_ = l_Vector_swap___redArg(v_xs_4891_, v_i_4892_, v_j_4893_);
    leanh::lean_dec(v_j_4893_);
    leanh::lean_dec(v_i_4892_);
    return v_res_4894_;
}
pub unsafe fn l_Vector_swap(
    mut v_00_u03b1_4895_: *mut leanh::LeanObject,
    mut v_n_4896_: *mut leanh::LeanObject,
    mut v_xs_4897_: *mut leanh::LeanObject,
    mut v_i_4898_: *mut leanh::LeanObject,
    mut v_j_4899_: *mut leanh::LeanObject,
    mut v_hi_4900_: *mut leanh::LeanObject,
    mut v_hj_4901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4902_ = lean_array_fswap(v_xs_4897_, v_i_4898_, v_j_4899_);
    return v___x_4902_;
}
pub unsafe fn l_Vector_swap___boxed(
    mut v_00_u03b1_4903_: *mut leanh::LeanObject,
    mut v_n_4904_: *mut leanh::LeanObject,
    mut v_xs_4905_: *mut leanh::LeanObject,
    mut v_i_4906_: *mut leanh::LeanObject,
    mut v_j_4907_: *mut leanh::LeanObject,
    mut v_hi_4908_: *mut leanh::LeanObject,
    mut v_hj_4909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4910_ = l_Vector_swap(
        v_00_u03b1_4903_,
        v_n_4904_,
        v_xs_4905_,
        v_i_4906_,
        v_j_4907_,
        v_hi_4908_,
        v_hj_4909_,
    );
    leanh::lean_dec(v_j_4907_);
    leanh::lean_dec(v_i_4906_);
    leanh::lean_dec(v_n_4904_);
    return v_res_4910_;
}
pub unsafe fn l_Vector_swapIfInBounds___redArg(
    mut v_xs_4911_: *mut leanh::LeanObject,
    mut v_i_4912_: *mut leanh::LeanObject,
    mut v_j_4913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4914_ = lean_array_swap(v_xs_4911_, v_i_4912_, v_j_4913_);
    return v___x_4914_;
}
pub unsafe fn l_Vector_swapIfInBounds___redArg___boxed(
    mut v_xs_4915_: *mut leanh::LeanObject,
    mut v_i_4916_: *mut leanh::LeanObject,
    mut v_j_4917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4918_ = l_Vector_swapIfInBounds___redArg(v_xs_4915_, v_i_4916_, v_j_4917_);
    leanh::lean_dec(v_j_4917_);
    leanh::lean_dec(v_i_4916_);
    return v_res_4918_;
}
pub unsafe fn l_Vector_swapIfInBounds(
    mut v_00_u03b1_4919_: *mut leanh::LeanObject,
    mut v_n_4920_: *mut leanh::LeanObject,
    mut v_xs_4921_: *mut leanh::LeanObject,
    mut v_i_4922_: *mut leanh::LeanObject,
    mut v_j_4923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4924_ = lean_array_swap(v_xs_4921_, v_i_4922_, v_j_4923_);
    return v___x_4924_;
}
pub unsafe fn l_Vector_swapIfInBounds___boxed(
    mut v_00_u03b1_4925_: *mut leanh::LeanObject,
    mut v_n_4926_: *mut leanh::LeanObject,
    mut v_xs_4927_: *mut leanh::LeanObject,
    mut v_i_4928_: *mut leanh::LeanObject,
    mut v_j_4929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4930_ = l_Vector_swapIfInBounds(
        v_00_u03b1_4925_,
        v_n_4926_,
        v_xs_4927_,
        v_i_4928_,
        v_j_4929_,
    );
    leanh::lean_dec(v_j_4929_);
    leanh::lean_dec(v_i_4928_);
    leanh::lean_dec(v_n_4926_);
    return v_res_4930_;
}
pub unsafe fn _init_l_Vector_swapAt___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4931_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__17_once),
        _init_l_Vector_set___auto__1___closed__17,
    );
    return v___x_4931_;
}
pub unsafe fn l_Vector_swapAt___redArg(
    mut v_xs_4932_: *mut leanh::LeanObject,
    mut v_i_4933_: *mut leanh::LeanObject,
    mut v_x_4934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_e_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_e_4935_ = lean_array_fget(v_xs_4932_, v_i_4933_);
    v_xs_x27_4936_ = lean_array_fset(v_xs_4932_, v_i_4933_, v_x_4934_);
    v___x_4937_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4937_, 0, v_e_4935_);
    leanh::lean_ctor_set(v___x_4937_, 1, v_xs_x27_4936_);
    return v___x_4937_;
}
pub unsafe fn l_Vector_swapAt___redArg___boxed(
    mut v_xs_4938_: *mut leanh::LeanObject,
    mut v_i_4939_: *mut leanh::LeanObject,
    mut v_x_4940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4941_ = l_Vector_swapAt___redArg(v_xs_4938_, v_i_4939_, v_x_4940_);
    leanh::lean_dec(v_i_4939_);
    return v_res_4941_;
}
pub unsafe fn l_Vector_swapAt(
    mut v_00_u03b1_4942_: *mut leanh::LeanObject,
    mut v_n_4943_: *mut leanh::LeanObject,
    mut v_xs_4944_: *mut leanh::LeanObject,
    mut v_i_4945_: *mut leanh::LeanObject,
    mut v_x_4946_: *mut leanh::LeanObject,
    mut v_hi_4947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_e_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_e_4948_ = lean_array_fget(v_xs_4944_, v_i_4945_);
    v_xs_x27_4949_ = lean_array_fset(v_xs_4944_, v_i_4945_, v_x_4946_);
    v___x_4950_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4950_, 0, v_e_4948_);
    leanh::lean_ctor_set(v___x_4950_, 1, v_xs_x27_4949_);
    return v___x_4950_;
}
pub unsafe fn l_Vector_swapAt___boxed(
    mut v_00_u03b1_4951_: *mut leanh::LeanObject,
    mut v_n_4952_: *mut leanh::LeanObject,
    mut v_xs_4953_: *mut leanh::LeanObject,
    mut v_i_4954_: *mut leanh::LeanObject,
    mut v_x_4955_: *mut leanh::LeanObject,
    mut v_hi_4956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4957_ = l_Vector_swapAt(
        v_00_u03b1_4951_,
        v_n_4952_,
        v_xs_4953_,
        v_i_4954_,
        v_x_4955_,
        v_hi_4956_,
    );
    leanh::lean_dec(v_i_4954_);
    leanh::lean_dec(v_n_4952_);
    return v_res_4957_;
}
pub unsafe fn l_Vector_swapAt_x21___redArg(
    mut v_xs_4962_: *mut leanh::LeanObject,
    mut v_i_4963_: *mut leanh::LeanObject,
    mut v_x_4964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: u8 = 0;
    let mut v_this_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4983_: u8 = 0;
    let mut v___x_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4987_: u8 = 0;
    let mut v_e_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4965_ = lean_array_get_size(v_xs_4962_);
                v___x_4966_ = lean_nat_dec_lt(v_i_4963_, v___x_4965_);
                if v___x_4966_ == 0 {
                    v_this_4967_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_this_4967_, 0, v_x_4964_);
                    leanh::lean_ctor_set(v_this_4967_, 1, v_xs_4962_);
                    v___x_4968_ = l_Vector_swapAt_x21___redArg___closed__0;
                    v___x_4969_ = l_Vector_swapAt_x21___redArg___closed__1;
                    v___x_4970_ = leanh::lean_unsigned_to_nat(438);
                    v___x_4971_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4972_ = l_Vector_swapAt_x21___redArg___closed__2;
                    v___x_4973_ = l_Nat_reprFast(v_i_4963_);
                    v___x_4974_ = lean_string_append(v___x_4972_, v___x_4973_);
                    leanh::lean_dec_ref(v___x_4973_);
                    v___x_4975_ = l_Vector_swapAt_x21___redArg___closed__3;
                    v___x_4976_ = lean_string_append(v___x_4974_, v___x_4975_);
                    v___x_4977_ = l_mkPanicMessageWithDecl(
                        v___x_4968_,
                        v___x_4969_,
                        v___x_4970_,
                        v___x_4971_,
                        v___x_4976_,
                    );
                    leanh::lean_dec_ref(v___x_4976_);
                    v___x_4978_ = l_panic___redArg(v_this_4967_, v___x_4977_);
                    leanh::lean_dec_ref_known(v_this_4967_, 2);
                    v_fst_4979_ = leanh::lean_ctor_get(v___x_4978_, 0);
                    v_snd_4980_ = leanh::lean_ctor_get(v___x_4978_, 1);
                    v_isSharedCheck_4987_ = (!leanh::lean_is_exclusive(v___x_4978_)) as u8;
                    if v_isSharedCheck_4987_ == 0 {
                        v___x_4982_ = v___x_4978_;
                        v_isShared_4983_ = v_isSharedCheck_4987_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4980_);
                        leanh::lean_inc(v_fst_4979_);
                        leanh::lean_dec(v___x_4978_);
                        v___x_4982_ = leanh::lean_box(0);
                        v_isShared_4983_ = v_isSharedCheck_4987_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_e_4988_ = lean_array_fget(v_xs_4962_, v_i_4963_);
                    v_xs_x27_4989_ = lean_array_fset(v_xs_4962_, v_i_4963_, v_x_4964_);
                    leanh::lean_dec(v_i_4963_);
                    v___x_4990_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4990_, 0, v_e_4988_);
                    leanh::lean_ctor_set(v___x_4990_, 1, v_xs_x27_4989_);
                    return v___x_4990_;
                }
            }
            1 => {
                if v_isShared_4983_ == 0 {
                    v___x_4985_ = v___x_4982_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4986_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4986_, 0, v_fst_4979_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4986_, 1, v_snd_4980_);
                    v___x_4985_ = v_reuseFailAlloc_4986_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4985_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Vector_swapAt_x21(
    mut v_00_u03b1_4991_: *mut leanh::LeanObject,
    mut v_n_4992_: *mut leanh::LeanObject,
    mut v_xs_4993_: *mut leanh::LeanObject,
    mut v_i_4994_: *mut leanh::LeanObject,
    mut v_x_4995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: u8 = 0;
    let mut v_this_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5014_: u8 = 0;
    let mut v___x_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5018_: u8 = 0;
    let mut v_e_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4996_ = lean_array_get_size(v_xs_4993_);
                v___x_4997_ = lean_nat_dec_lt(v_i_4994_, v___x_4996_);
                if v___x_4997_ == 0 {
                    v_this_4998_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_this_4998_, 0, v_x_4995_);
                    leanh::lean_ctor_set(v_this_4998_, 1, v_xs_4993_);
                    v___x_4999_ = l_Vector_swapAt_x21___redArg___closed__0;
                    v___x_5000_ = l_Vector_swapAt_x21___redArg___closed__1;
                    v___x_5001_ = leanh::lean_unsigned_to_nat(438);
                    v___x_5002_ = leanh::lean_unsigned_to_nat(4);
                    v___x_5003_ = l_Vector_swapAt_x21___redArg___closed__2;
                    v___x_5004_ = l_Nat_reprFast(v_i_4994_);
                    v___x_5005_ = lean_string_append(v___x_5003_, v___x_5004_);
                    leanh::lean_dec_ref(v___x_5004_);
                    v___x_5006_ = l_Vector_swapAt_x21___redArg___closed__3;
                    v___x_5007_ = lean_string_append(v___x_5005_, v___x_5006_);
                    v___x_5008_ = l_mkPanicMessageWithDecl(
                        v___x_4999_,
                        v___x_5000_,
                        v___x_5001_,
                        v___x_5002_,
                        v___x_5007_,
                    );
                    leanh::lean_dec_ref(v___x_5007_);
                    v___x_5009_ = l_panic___redArg(v_this_4998_, v___x_5008_);
                    leanh::lean_dec_ref_known(v_this_4998_, 2);
                    v_fst_5010_ = leanh::lean_ctor_get(v___x_5009_, 0);
                    v_snd_5011_ = leanh::lean_ctor_get(v___x_5009_, 1);
                    v_isSharedCheck_5018_ = (!leanh::lean_is_exclusive(v___x_5009_)) as u8;
                    if v_isSharedCheck_5018_ == 0 {
                        v___x_5013_ = v___x_5009_;
                        v_isShared_5014_ = v_isSharedCheck_5018_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5011_);
                        leanh::lean_inc(v_fst_5010_);
                        leanh::lean_dec(v___x_5009_);
                        v___x_5013_ = leanh::lean_box(0);
                        v_isShared_5014_ = v_isSharedCheck_5018_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_e_5019_ = lean_array_fget(v_xs_4993_, v_i_4994_);
                    v_xs_x27_5020_ = lean_array_fset(v_xs_4993_, v_i_4994_, v_x_4995_);
                    leanh::lean_dec(v_i_4994_);
                    v___x_5021_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5021_, 0, v_e_5019_);
                    leanh::lean_ctor_set(v___x_5021_, 1, v_xs_x27_5020_);
                    return v___x_5021_;
                }
            }
            1 => {
                if v_isShared_5014_ == 0 {
                    v___x_5016_ = v___x_5013_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5017_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5017_, 0, v_fst_5010_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5017_, 1, v_snd_5011_);
                    v___x_5016_ = v_reuseFailAlloc_5017_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5016_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Vector_swapAt_x21___boxed(
    mut v_00_u03b1_5022_: *mut leanh::LeanObject,
    mut v_n_5023_: *mut leanh::LeanObject,
    mut v_xs_5024_: *mut leanh::LeanObject,
    mut v_i_5025_: *mut leanh::LeanObject,
    mut v_x_5026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5027_ = l_Vector_swapAt_x21(
        v_00_u03b1_5022_,
        v_n_5023_,
        v_xs_5024_,
        v_i_5025_,
        v_x_5026_,
    );
    leanh::lean_dec(v_n_5023_);
    return v_res_5027_;
}
pub unsafe fn l_Vector_range(
    mut v_n_5028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5029_ = l_Array_range(v_n_5028_);
    return v___x_5029_;
}
pub unsafe fn l_Vector_range_x27(
    mut v_start_5030_: *mut leanh::LeanObject,
    mut v_size_5031_: *mut leanh::LeanObject,
    mut v_step_5032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5033_ = l_Array_range_x27(v_start_5030_, v_size_5031_, v_step_5032_);
    return v___x_5033_;
}
pub unsafe fn l_Vector_isEqv___redArg(
    mut v_n_5034_: *mut leanh::LeanObject,
    mut v_xs_5035_: *mut leanh::LeanObject,
    mut v_ys_5036_: *mut leanh::LeanObject,
    mut v_r_5037_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5038_: u8 = 0;
    v___x_5038_ = l_Array_isEqvAux___redArg(v_xs_5035_, v_ys_5036_, v_r_5037_, v_n_5034_);
    return v___x_5038_;
}
pub unsafe fn l_Vector_isEqv___redArg___boxed(
    mut v_n_5039_: *mut leanh::LeanObject,
    mut v_xs_5040_: *mut leanh::LeanObject,
    mut v_ys_5041_: *mut leanh::LeanObject,
    mut v_r_5042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5043_: u8 = 0;
    let mut v_r_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5043_ = l_Vector_isEqv___redArg(v_n_5039_, v_xs_5040_, v_ys_5041_, v_r_5042_);
    leanh::lean_dec_ref(v_ys_5041_);
    leanh::lean_dec_ref(v_xs_5040_);
    v_r_5044_ = leanh::lean_box((v_res_5043_) as usize);
    return v_r_5044_;
}
pub unsafe fn l_Vector_isEqv(
    mut v_00_u03b1_5045_: *mut leanh::LeanObject,
    mut v_n_5046_: *mut leanh::LeanObject,
    mut v_xs_5047_: *mut leanh::LeanObject,
    mut v_ys_5048_: *mut leanh::LeanObject,
    mut v_r_5049_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5050_: u8 = 0;
    v___x_5050_ = l_Array_isEqvAux___redArg(v_xs_5047_, v_ys_5048_, v_r_5049_, v_n_5046_);
    return v___x_5050_;
}
pub unsafe fn l_Vector_isEqv___boxed(
    mut v_00_u03b1_5051_: *mut leanh::LeanObject,
    mut v_n_5052_: *mut leanh::LeanObject,
    mut v_xs_5053_: *mut leanh::LeanObject,
    mut v_ys_5054_: *mut leanh::LeanObject,
    mut v_r_5055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5056_: u8 = 0;
    let mut v_r_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5056_ = l_Vector_isEqv(
        v_00_u03b1_5051_,
        v_n_5052_,
        v_xs_5053_,
        v_ys_5054_,
        v_r_5055_,
    );
    leanh::lean_dec_ref(v_ys_5054_);
    leanh::lean_dec_ref(v_xs_5053_);
    v_r_5057_ = leanh::lean_box((v_res_5056_) as usize);
    return v_r_5057_;
}
pub unsafe fn l_Vector_instBEq___redArg___lam__0(
    mut v_inst_5058_: *mut leanh::LeanObject,
    mut v_x1_5059_: *mut leanh::LeanObject,
    mut v_x2_5060_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: u8 = 0;
    v___x_5061_ = leanh::lean_apply_2(v_inst_5058_, v_x1_5059_, v_x2_5060_);
    v___x_5062_ = (leanh::lean_unbox(v___x_5061_) as u8);
    return v___x_5062_;
}
pub unsafe fn l_Vector_instBEq___redArg___lam__0___boxed(
    mut v_inst_5063_: *mut leanh::LeanObject,
    mut v_x1_5064_: *mut leanh::LeanObject,
    mut v_x2_5065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5066_: u8 = 0;
    let mut v_r_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5066_ = l_Vector_instBEq___redArg___lam__0(v_inst_5063_, v_x1_5064_, v_x2_5065_);
    v_r_5067_ = leanh::lean_box((v_res_5066_) as usize);
    return v_r_5067_;
}
pub unsafe fn l_Vector_instBEq___redArg___lam__1(
    mut v___f_5068_: *mut leanh::LeanObject,
    mut v_n_5069_: *mut leanh::LeanObject,
    mut v_xs_5070_: *mut leanh::LeanObject,
    mut v_ys_5071_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5072_: u8 = 0;
    v___x_5072_ = l_Array_isEqvAux___redArg(v_xs_5070_, v_ys_5071_, v___f_5068_, v_n_5069_);
    return v___x_5072_;
}
pub unsafe fn l_Vector_instBEq___redArg___lam__1___boxed(
    mut v___f_5073_: *mut leanh::LeanObject,
    mut v_n_5074_: *mut leanh::LeanObject,
    mut v_xs_5075_: *mut leanh::LeanObject,
    mut v_ys_5076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5077_: u8 = 0;
    let mut v_r_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5077_ =
        l_Vector_instBEq___redArg___lam__1(v___f_5073_, v_n_5074_, v_xs_5075_, v_ys_5076_);
    leanh::lean_dec_ref(v_ys_5076_);
    leanh::lean_dec_ref(v_xs_5075_);
    v_r_5078_ = leanh::lean_box((v_res_5077_) as usize);
    return v_r_5078_;
}
pub unsafe fn l_Vector_instBEq___redArg(
    mut v_n_5079_: *mut leanh::LeanObject,
    mut v_inst_5080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5081_ = leanh::lean_alloc_closure(
        l_Vector_instBEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_5081_, 0, v_inst_5080_);
    v___f_5082_ = leanh::lean_alloc_closure(
        l_Vector_instBEq___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_5082_, 0, v___f_5081_);
    leanh::lean_closure_set(v___f_5082_, 1, v_n_5079_);
    return v___f_5082_;
}
pub unsafe fn l_Vector_instBEq(
    mut v_00_u03b1_5083_: *mut leanh::LeanObject,
    mut v_n_5084_: *mut leanh::LeanObject,
    mut v_inst_5085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5086_ = l_Vector_instBEq___redArg(v_n_5084_, v_inst_5085_);
    return v___x_5086_;
}
pub unsafe fn l_Vector_reverse___redArg(
    mut v_xs_5087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5088_ = l_Array_reverse___redArg(v_xs_5087_);
    return v___x_5088_;
}
pub unsafe fn l_Vector_reverse(
    mut v_00_u03b1_5089_: *mut leanh::LeanObject,
    mut v_n_5090_: *mut leanh::LeanObject,
    mut v_xs_5091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5092_ = l_Array_reverse___redArg(v_xs_5091_);
    return v___x_5092_;
}
pub unsafe fn l_Vector_reverse___boxed(
    mut v_00_u03b1_5093_: *mut leanh::LeanObject,
    mut v_n_5094_: *mut leanh::LeanObject,
    mut v_xs_5095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5096_ = l_Vector_reverse(v_00_u03b1_5093_, v_n_5094_, v_xs_5095_);
    leanh::lean_dec(v_n_5094_);
    return v_res_5096_;
}
pub unsafe fn _init_l_Vector_eraseIdx___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5097_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__17_once),
        _init_l_Vector_set___auto__1___closed__17,
    );
    return v___x_5097_;
}
pub unsafe fn l_Vector_eraseIdx___redArg(
    mut v_xs_5098_: *mut leanh::LeanObject,
    mut v_i_5099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5100_ = l_Array_eraseIdx___redArg(v_xs_5098_, v_i_5099_);
    return v___x_5100_;
}
pub unsafe fn l_Vector_eraseIdx(
    mut v_00_u03b1_5101_: *mut leanh::LeanObject,
    mut v_n_5102_: *mut leanh::LeanObject,
    mut v_xs_5103_: *mut leanh::LeanObject,
    mut v_i_5104_: *mut leanh::LeanObject,
    mut v_h_5105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5106_ = l_Array_eraseIdx___redArg(v_xs_5103_, v_i_5104_);
    return v___x_5106_;
}
pub unsafe fn l_Vector_eraseIdx___boxed(
    mut v_00_u03b1_5107_: *mut leanh::LeanObject,
    mut v_n_5108_: *mut leanh::LeanObject,
    mut v_xs_5109_: *mut leanh::LeanObject,
    mut v_i_5110_: *mut leanh::LeanObject,
    mut v_h_5111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5112_ = l_Vector_eraseIdx(
        v_00_u03b1_5107_,
        v_n_5108_,
        v_xs_5109_,
        v_i_5110_,
        v_h_5111_,
    );
    leanh::lean_dec(v_n_5108_);
    return v_res_5112_;
}
pub unsafe fn _init_l_Vector_eraseIdx_x21___redArg___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5116_ = l_Vector_eraseIdx_x21___redArg___closed__2;
    v___x_5117_ = leanh::lean_unsigned_to_nat(4);
    v___x_5118_ = leanh::lean_unsigned_to_nat(395);
    v___x_5119_ = l_Vector_eraseIdx_x21___redArg___closed__1;
    v___x_5120_ = l_Vector_eraseIdx_x21___redArg___closed__0;
    v___x_5121_ = l_mkPanicMessageWithDecl(
        v___x_5120_,
        v___x_5119_,
        v___x_5118_,
        v___x_5117_,
        v___x_5116_,
    );
    return v___x_5121_;
}
pub unsafe fn l_Vector_eraseIdx_x21___redArg(
    mut v_n_5122_: *mut leanh::LeanObject,
    mut v_xs_5123_: *mut leanh::LeanObject,
    mut v_i_5124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5125_: u8 = 0;
    v___x_5125_ = lean_nat_dec_lt(v_i_5124_, v_n_5122_);
    if v___x_5125_ == 0 {
        let mut v_this_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_i_5124_);
        v_this_5126_ = lean_array_pop(v_xs_5123_);
        v___x_5127_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Vector_eraseIdx_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Vector_eraseIdx_x21___redArg___closed__3_once),
            _init_l_Vector_eraseIdx_x21___redArg___closed__3,
        );
        v___x_5128_ = l_panic___redArg(v_this_5126_, v___x_5127_);
        leanh::lean_dec_ref(v_this_5126_);
        return v___x_5128_;
    } else {
        let mut v___x_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5129_ = l_Array_eraseIdx___redArg(v_xs_5123_, v_i_5124_);
        return v___x_5129_;
    }
}
pub unsafe fn l_Vector_eraseIdx_x21___redArg___boxed(
    mut v_n_5130_: *mut leanh::LeanObject,
    mut v_xs_5131_: *mut leanh::LeanObject,
    mut v_i_5132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5133_ = l_Vector_eraseIdx_x21___redArg(v_n_5130_, v_xs_5131_, v_i_5132_);
    leanh::lean_dec(v_n_5130_);
    return v_res_5133_;
}
pub unsafe fn l_Vector_eraseIdx_x21(
    mut v_00_u03b1_5134_: *mut leanh::LeanObject,
    mut v_n_5135_: *mut leanh::LeanObject,
    mut v_xs_5136_: *mut leanh::LeanObject,
    mut v_i_5137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5138_: u8 = 0;
    v___x_5138_ = lean_nat_dec_lt(v_i_5137_, v_n_5135_);
    if v___x_5138_ == 0 {
        let mut v_this_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_i_5137_);
        v_this_5139_ = lean_array_pop(v_xs_5136_);
        v___x_5140_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Vector_eraseIdx_x21___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Vector_eraseIdx_x21___redArg___closed__3_once),
            _init_l_Vector_eraseIdx_x21___redArg___closed__3,
        );
        v___x_5141_ = l_panic___redArg(v_this_5139_, v___x_5140_);
        leanh::lean_dec_ref(v_this_5139_);
        return v___x_5141_;
    } else {
        let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5142_ = l_Array_eraseIdx___redArg(v_xs_5136_, v_i_5137_);
        return v___x_5142_;
    }
}
pub unsafe fn l_Vector_eraseIdx_x21___boxed(
    mut v_00_u03b1_5143_: *mut leanh::LeanObject,
    mut v_n_5144_: *mut leanh::LeanObject,
    mut v_xs_5145_: *mut leanh::LeanObject,
    mut v_i_5146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5147_ = l_Vector_eraseIdx_x21(v_00_u03b1_5143_, v_n_5144_, v_xs_5145_, v_i_5146_);
    leanh::lean_dec(v_n_5144_);
    return v_res_5147_;
}
pub unsafe fn _init_l_Vector_insertIdx___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5148_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Vector_set___auto__1___closed__17_once),
        _init_l_Vector_set___auto__1___closed__17,
    );
    return v___x_5148_;
}
pub unsafe fn l_Vector_insertIdx___redArg(
    mut v_xs_5149_: *mut leanh::LeanObject,
    mut v_i_5150_: *mut leanh::LeanObject,
    mut v_x_5151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_j_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_as_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_j_5152_ = lean_array_get_size(v_xs_5149_);
    v_as_5153_ = lean_array_push(v_xs_5149_, v_x_5151_);
    v___x_5154_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
        leanh::lean_box(0),
        v_i_5150_,
        v_as_5153_,
        v_j_5152_,
    );
    return v___x_5154_;
}
pub unsafe fn l_Vector_insertIdx___redArg___boxed(
    mut v_xs_5155_: *mut leanh::LeanObject,
    mut v_i_5156_: *mut leanh::LeanObject,
    mut v_x_5157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5158_ = l_Vector_insertIdx___redArg(v_xs_5155_, v_i_5156_, v_x_5157_);
    leanh::lean_dec(v_i_5156_);
    return v_res_5158_;
}
pub unsafe fn l_Vector_insertIdx(
    mut v_00_u03b1_5159_: *mut leanh::LeanObject,
    mut v_n_5160_: *mut leanh::LeanObject,
    mut v_xs_5161_: *mut leanh::LeanObject,
    mut v_i_5162_: *mut leanh::LeanObject,
    mut v_x_5163_: *mut leanh::LeanObject,
    mut v_h_5164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_j_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_as_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_j_5165_ = lean_array_get_size(v_xs_5161_);
    v_as_5166_ = lean_array_push(v_xs_5161_, v_x_5163_);
    v___x_5167_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
        leanh::lean_box(0),
        v_i_5162_,
        v_as_5166_,
        v_j_5165_,
    );
    return v___x_5167_;
}
pub unsafe fn l_Vector_insertIdx___boxed(
    mut v_00_u03b1_5168_: *mut leanh::LeanObject,
    mut v_n_5169_: *mut leanh::LeanObject,
    mut v_xs_5170_: *mut leanh::LeanObject,
    mut v_i_5171_: *mut leanh::LeanObject,
    mut v_x_5172_: *mut leanh::LeanObject,
    mut v_h_5173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5174_ = l_Vector_insertIdx(
        v_00_u03b1_5168_,
        v_n_5169_,
        v_xs_5170_,
        v_i_5171_,
        v_x_5172_,
        v_h_5173_,
    );
    leanh::lean_dec(v_i_5171_);
    leanh::lean_dec(v_n_5169_);
    return v_res_5174_;
}
pub unsafe fn _init_l_Vector_insertIdx_x21___redArg___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5176_ = l_Vector_eraseIdx_x21___redArg___closed__2;
    v___x_5177_ = leanh::lean_unsigned_to_nat(4);
    v___x_5178_ = leanh::lean_unsigned_to_nat(408);
    v___x_5179_ = l_Vector_insertIdx_x21___redArg___closed__0;
    v___x_5180_ = l_Vector_eraseIdx_x21___redArg___closed__0;
    v___x_5181_ = l_mkPanicMessageWithDecl(
        v___x_5180_,
        v___x_5179_,
        v___x_5178_,
        v___x_5177_,
        v___x_5176_,
    );
    return v___x_5181_;
}
pub unsafe fn l_Vector_insertIdx_x21___redArg(
    mut v_n_5182_: *mut leanh::LeanObject,
    mut v_xs_5183_: *mut leanh::LeanObject,
    mut v_i_5184_: *mut leanh::LeanObject,
    mut v_x_5185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5186_: u8 = 0;
    v___x_5186_ = lean_nat_dec_le(v_i_5184_, v_n_5182_);
    if v___x_5186_ == 0 {
        let mut v_this_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_this_5187_ = lean_array_push(v_xs_5183_, v_x_5185_);
        v___x_5188_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Vector_insertIdx_x21___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Vector_insertIdx_x21___redArg___closed__1_once),
            _init_l_Vector_insertIdx_x21___redArg___closed__1,
        );
        v___x_5189_ = l_panic___redArg(v_this_5187_, v___x_5188_);
        leanh::lean_dec_ref(v_this_5187_);
        return v___x_5189_;
    } else {
        let mut v_j_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_as_5191_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_j_5190_ = lean_array_get_size(v_xs_5183_);
        v_as_5191_ = lean_array_push(v_xs_5183_, v_x_5185_);
        v___x_5192_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
            leanh::lean_box(0),
            v_i_5184_,
            v_as_5191_,
            v_j_5190_,
        );
        return v___x_5192_;
    }
}
pub unsafe fn l_Vector_insertIdx_x21___redArg___boxed(
    mut v_n_5193_: *mut leanh::LeanObject,
    mut v_xs_5194_: *mut leanh::LeanObject,
    mut v_i_5195_: *mut leanh::LeanObject,
    mut v_x_5196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5197_ = l_Vector_insertIdx_x21___redArg(v_n_5193_, v_xs_5194_, v_i_5195_, v_x_5196_);
    leanh::lean_dec(v_i_5195_);
    leanh::lean_dec(v_n_5193_);
    return v_res_5197_;
}
pub unsafe fn l_Vector_insertIdx_x21(
    mut v_00_u03b1_5198_: *mut leanh::LeanObject,
    mut v_n_5199_: *mut leanh::LeanObject,
    mut v_xs_5200_: *mut leanh::LeanObject,
    mut v_i_5201_: *mut leanh::LeanObject,
    mut v_x_5202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5203_: u8 = 0;
    v___x_5203_ = lean_nat_dec_le(v_i_5201_, v_n_5199_);
    if v___x_5203_ == 0 {
        let mut v_this_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5205_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_this_5204_ = lean_array_push(v_xs_5200_, v_x_5202_);
        v___x_5205_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Vector_insertIdx_x21___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Vector_insertIdx_x21___redArg___closed__1_once),
            _init_l_Vector_insertIdx_x21___redArg___closed__1,
        );
        v___x_5206_ = l_panic___redArg(v_this_5204_, v___x_5205_);
        leanh::lean_dec_ref(v_this_5204_);
        return v___x_5206_;
    } else {
        let mut v_j_5207_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_as_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_j_5207_ = lean_array_get_size(v_xs_5200_);
        v_as_5208_ = lean_array_push(v_xs_5200_, v_x_5202_);
        v___x_5209_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
            leanh::lean_box(0),
            v_i_5201_,
            v_as_5208_,
            v_j_5207_,
        );
        return v___x_5209_;
    }
}
pub unsafe fn l_Vector_insertIdx_x21___boxed(
    mut v_00_u03b1_5210_: *mut leanh::LeanObject,
    mut v_n_5211_: *mut leanh::LeanObject,
    mut v_xs_5212_: *mut leanh::LeanObject,
    mut v_i_5213_: *mut leanh::LeanObject,
    mut v_x_5214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5215_ = l_Vector_insertIdx_x21(
        v_00_u03b1_5210_,
        v_n_5211_,
        v_xs_5212_,
        v_i_5213_,
        v_x_5214_,
    );
    leanh::lean_dec(v_i_5213_);
    leanh::lean_dec(v_n_5211_);
    return v_res_5215_;
}
pub unsafe fn l_Vector_tail___redArg(
    mut v_n_5216_: *mut leanh::LeanObject,
    mut v_xs_5217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5218_ = leanh::lean_unsigned_to_nat(1);
    v___x_5219_ = l_Array_extract___redArg(v_xs_5217_, v___x_5218_, v_n_5216_);
    return v___x_5219_;
}
pub unsafe fn l_Vector_tail___redArg___boxed(
    mut v_n_5220_: *mut leanh::LeanObject,
    mut v_xs_5221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5222_ = l_Vector_tail___redArg(v_n_5220_, v_xs_5221_);
    leanh::lean_dec_ref(v_xs_5221_);
    return v_res_5222_;
}
pub unsafe fn l_Vector_tail(
    mut v_00_u03b1_5223_: *mut leanh::LeanObject,
    mut v_n_5224_: *mut leanh::LeanObject,
    mut v_xs_5225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5226_ = leanh::lean_unsigned_to_nat(1);
    v___x_5227_ = l_Array_extract___redArg(v_xs_5225_, v___x_5226_, v_n_5224_);
    return v___x_5227_;
}
pub unsafe fn l_Vector_tail___boxed(
    mut v_00_u03b1_5228_: *mut leanh::LeanObject,
    mut v_n_5229_: *mut leanh::LeanObject,
    mut v_xs_5230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5231_ = l_Vector_tail(v_00_u03b1_5228_, v_n_5229_, v_xs_5230_);
    leanh::lean_dec_ref(v_xs_5230_);
    return v_res_5231_;
}
pub unsafe fn l_Vector_finIdxOf_x3f___redArg(
    mut v_inst_5232_: *mut leanh::LeanObject,
    mut v_xs_5233_: *mut leanh::LeanObject,
    mut v_x_5234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5239_: u8 = 0;
    let mut v___x_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5243_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5235_ = l_Array_finIdxOf_x3f___redArg(v_inst_5232_, v_xs_5233_, v_x_5234_);
                if leanh::lean_obj_tag(v___x_5235_) == 0 {
                    return v___x_5235_;
                } else {
                    v_val_5236_ = leanh::lean_ctor_get(v___x_5235_, 0);
                    v_isSharedCheck_5243_ = (!leanh::lean_is_exclusive(v___x_5235_)) as u8;
                    if v_isSharedCheck_5243_ == 0 {
                        v___x_5238_ = v___x_5235_;
                        v_isShared_5239_ = v_isSharedCheck_5243_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5236_);
                        leanh::lean_dec(v___x_5235_);
                        v___x_5238_ = leanh::lean_box(0);
                        v_isShared_5239_ = v_isSharedCheck_5243_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5239_ == 0 {
                    v___x_5241_ = v___x_5238_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5242_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5242_, 0, v_val_5236_);
                    v___x_5241_ = v_reuseFailAlloc_5242_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5241_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Vector_finIdxOf_x3f___redArg___boxed(
    mut v_inst_5244_: *mut leanh::LeanObject,
    mut v_xs_5245_: *mut leanh::LeanObject,
    mut v_x_5246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5247_ = l_Vector_finIdxOf_x3f___redArg(v_inst_5244_, v_xs_5245_, v_x_5246_);
    leanh::lean_dec_ref(v_xs_5245_);
    return v_res_5247_;
}
pub unsafe fn l_Vector_finIdxOf_x3f(
    mut v_00_u03b1_5248_: *mut leanh::LeanObject,
    mut v_n_5249_: *mut leanh::LeanObject,
    mut v_inst_5250_: *mut leanh::LeanObject,
    mut v_xs_5251_: *mut leanh::LeanObject,
    mut v_x_5252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5257_: u8 = 0;
    let mut v___x_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5261_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5253_ = l_Array_finIdxOf_x3f___redArg(v_inst_5250_, v_xs_5251_, v_x_5252_);
                if leanh::lean_obj_tag(v___x_5253_) == 0 {
                    return v___x_5253_;
                } else {
                    v_val_5254_ = leanh::lean_ctor_get(v___x_5253_, 0);
                    v_isSharedCheck_5261_ = (!leanh::lean_is_exclusive(v___x_5253_)) as u8;
                    if v_isSharedCheck_5261_ == 0 {
                        v___x_5256_ = v___x_5253_;
                        v_isShared_5257_ = v_isSharedCheck_5261_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5254_);
                        leanh::lean_dec(v___x_5253_);
                        v___x_5256_ = leanh::lean_box(0);
                        v_isShared_5257_ = v_isSharedCheck_5261_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5257_ == 0 {
                    v___x_5259_ = v___x_5256_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5260_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5260_, 0, v_val_5254_);
                    v___x_5259_ = v_reuseFailAlloc_5260_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5259_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Vector_finIdxOf_x3f___boxed(
    mut v_00_u03b1_5262_: *mut leanh::LeanObject,
    mut v_n_5263_: *mut leanh::LeanObject,
    mut v_inst_5264_: *mut leanh::LeanObject,
    mut v_xs_5265_: *mut leanh::LeanObject,
    mut v_x_5266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5267_ = l_Vector_finIdxOf_x3f(
        v_00_u03b1_5262_,
        v_n_5263_,
        v_inst_5264_,
        v_xs_5265_,
        v_x_5266_,
    );
    leanh::lean_dec_ref(v_xs_5265_);
    leanh::lean_dec(v_n_5263_);
    return v_res_5267_;
}
pub unsafe fn l_Vector_findFinIdx_x3f___redArg(
    mut v_p_5268_: *mut leanh::LeanObject,
    mut v_xs_5269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5275_: u8 = 0;
    let mut v___x_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5279_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5270_ = leanh::lean_unsigned_to_nat(0);
                v___x_5271_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(
                    leanh::lean_box(0),
                    v_p_5268_,
                    v_xs_5269_,
                    v___x_5270_,
                );
                if leanh::lean_obj_tag(v___x_5271_) == 0 {
                    return v___x_5271_;
                } else {
                    v_val_5272_ = leanh::lean_ctor_get(v___x_5271_, 0);
                    v_isSharedCheck_5279_ = (!leanh::lean_is_exclusive(v___x_5271_)) as u8;
                    if v_isSharedCheck_5279_ == 0 {
                        v___x_5274_ = v___x_5271_;
                        v_isShared_5275_ = v_isSharedCheck_5279_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5272_);
                        leanh::lean_dec(v___x_5271_);
                        v___x_5274_ = leanh::lean_box(0);
                        v_isShared_5275_ = v_isSharedCheck_5279_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5275_ == 0 {
                    v___x_5277_ = v___x_5274_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5278_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5278_, 0, v_val_5272_);
                    v___x_5277_ = v_reuseFailAlloc_5278_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5277_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Vector_findFinIdx_x3f___redArg___boxed(
    mut v_p_5280_: *mut leanh::LeanObject,
    mut v_xs_5281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5282_ = l_Vector_findFinIdx_x3f___redArg(v_p_5280_, v_xs_5281_);
    leanh::lean_dec_ref(v_xs_5281_);
    return v_res_5282_;
}
pub unsafe fn l_Vector_findFinIdx_x3f(
    mut v_00_u03b1_5283_: *mut leanh::LeanObject,
    mut v_n_5284_: *mut leanh::LeanObject,
    mut v_p_5285_: *mut leanh::LeanObject,
    mut v_xs_5286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5292_: u8 = 0;
    let mut v___x_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5296_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5287_ = leanh::lean_unsigned_to_nat(0);
                v___x_5288_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(
                    leanh::lean_box(0),
                    v_p_5285_,
                    v_xs_5286_,
                    v___x_5287_,
                );
                if leanh::lean_obj_tag(v___x_5288_) == 0 {
                    return v___x_5288_;
                } else {
                    v_val_5289_ = leanh::lean_ctor_get(v___x_5288_, 0);
                    v_isSharedCheck_5296_ = (!leanh::lean_is_exclusive(v___x_5288_)) as u8;
                    if v_isSharedCheck_5296_ == 0 {
                        v___x_5291_ = v___x_5288_;
                        v_isShared_5292_ = v_isSharedCheck_5296_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5289_);
                        leanh::lean_dec(v___x_5288_);
                        v___x_5291_ = leanh::lean_box(0);
                        v_isShared_5292_ = v_isSharedCheck_5296_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5292_ == 0 {
                    v___x_5294_ = v___x_5291_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5295_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5295_, 0, v_val_5289_);
                    v___x_5294_ = v_reuseFailAlloc_5295_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5294_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Vector_findFinIdx_x3f___boxed(
    mut v_00_u03b1_5297_: *mut leanh::LeanObject,
    mut v_n_5298_: *mut leanh::LeanObject,
    mut v_p_5299_: *mut leanh::LeanObject,
    mut v_xs_5300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5301_ = l_Vector_findFinIdx_x3f(v_00_u03b1_5297_, v_n_5298_, v_p_5299_, v_xs_5300_);
    leanh::lean_dec_ref(v_xs_5300_);
    leanh::lean_dec(v_n_5298_);
    return v_res_5301_;
}
pub unsafe fn l_Vector_findM_x3f___redArg___lam__0(
    mut v_toPure_5302_: *mut leanh::LeanObject,
    mut v_____s_5303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_5304_ = leanh::lean_ctor_get(v_____s_5303_, 0);
    leanh::lean_inc(v_fst_5304_);
    leanh::lean_dec_ref(v_____s_5303_);
    if leanh::lean_obj_tag(v_fst_5304_) == 0 {
        let mut v___x_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5305_ = leanh::lean_box(0);
        v___x_5306_ =
            leanh::lean_apply_2(v_toPure_5302_, leanh::lean_box(0), v___x_5305_);
        return v___x_5306_;
    } else {
        let mut v_val_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5307_ = leanh::lean_ctor_get(v_fst_5304_, 0);
        leanh::lean_inc(v_val_5307_);
        leanh::lean_dec_ref_known(v_fst_5304_, 1);
        v___x_5308_ =
            leanh::lean_apply_2(v_toPure_5302_, leanh::lean_box(0), v_val_5307_);
        return v___x_5308_;
    }
}
pub unsafe fn l_Vector_findM_x3f___redArg___lam__1(
    mut v___x_5309_: *mut leanh::LeanObject,
    mut v_toPure_5310_: *mut leanh::LeanObject,
    mut v_a_5311_: *mut leanh::LeanObject,
    mut v___x_5312_: *mut leanh::LeanObject,
    mut v_____do__lift_5313_: u8,
) -> *mut leanh::LeanObject {
    if v_____do__lift_5313_ == 0 {
        let mut v___x_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_5311_);
        v___x_5314_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5314_, 0, v___x_5309_);
        v___x_5315_ =
            leanh::lean_apply_2(v_toPure_5310_, leanh::lean_box(0), v___x_5314_);
        return v___x_5315_;
    } else {
        let mut v___x_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5320_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_5309_);
        v___x_5316_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5316_, 0, v_a_5311_);
        v___x_5317_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5317_, 0, v___x_5316_);
        v___x_5318_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5318_, 0, v___x_5317_);
        leanh::lean_ctor_set(v___x_5318_, 1, v___x_5312_);
        v___x_5319_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5319_, 0, v___x_5318_);
        v___x_5320_ =
            leanh::lean_apply_2(v_toPure_5310_, leanh::lean_box(0), v___x_5319_);
        return v___x_5320_;
    }
}
pub unsafe fn l_Vector_findM_x3f___redArg___lam__1___boxed(
    mut v___x_5321_: *mut leanh::LeanObject,
    mut v_toPure_5322_: *mut leanh::LeanObject,
    mut v_a_5323_: *mut leanh::LeanObject,
    mut v___x_5324_: *mut leanh::LeanObject,
    mut v_____do__lift_5325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_124__boxed_5326_: u8 = 0;
    let mut v_res_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_124__boxed_5326_ = (leanh::lean_unbox(v_____do__lift_5325_) as u8);
    v_res_5327_ = l_Vector_findM_x3f___redArg___lam__1(
        v___x_5321_,
        v_toPure_5322_,
        v_a_5323_,
        v___x_5324_,
        v_____do__lift_124__boxed_5326_,
    );
    return v_res_5327_;
}
pub unsafe fn l_Vector_findM_x3f___redArg___lam__2(
    mut v___x_5328_: *mut leanh::LeanObject,
    mut v_toPure_5329_: *mut leanh::LeanObject,
    mut v___x_5330_: *mut leanh::LeanObject,
    mut v_f_5331_: *mut leanh::LeanObject,
    mut v_toBind_5332_: *mut leanh::LeanObject,
    mut v_a_5333_: *mut leanh::LeanObject,
    mut v_x_5334_: *mut leanh::LeanObject,
    mut v___y_5335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_5333_);
    v___f_5336_ = leanh::lean_alloc_closure(
        l_Vector_findM_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_5336_, 0, v___x_5328_);
    leanh::lean_closure_set(v___f_5336_, 1, v_toPure_5329_);
    leanh::lean_closure_set(v___f_5336_, 2, v_a_5333_);
    leanh::lean_closure_set(v___f_5336_, 3, v___x_5330_);
    v___x_5337_ = leanh::lean_apply_1(v_f_5331_, v_a_5333_);
    v___x_5338_ = leanh::lean_apply_4(
        v_toBind_5332_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5337_,
        v___f_5336_,
    );
    return v___x_5338_;
}
pub unsafe fn l_Vector_findM_x3f___redArg___lam__2___boxed(
    mut v___x_5339_: *mut leanh::LeanObject,
    mut v_toPure_5340_: *mut leanh::LeanObject,
    mut v___x_5341_: *mut leanh::LeanObject,
    mut v_f_5342_: *mut leanh::LeanObject,
    mut v_toBind_5343_: *mut leanh::LeanObject,
    mut v_a_5344_: *mut leanh::LeanObject,
    mut v_x_5345_: *mut leanh::LeanObject,
    mut v___y_5346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5347_ = l_Vector_findM_x3f___redArg___lam__2(
        v___x_5339_,
        v_toPure_5340_,
        v___x_5341_,
        v_f_5342_,
        v_toBind_5343_,
        v_a_5344_,
        v_x_5345_,
        v___y_5346_,
    );
    leanh::lean_dec_ref(v___y_5346_);
    return v_res_5347_;
}
pub unsafe fn l_Vector_findM_x3f___redArg(
    mut v_inst_5351_: *mut leanh::LeanObject,
    mut v_f_5352_: *mut leanh::LeanObject,
    mut v_as_5353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5361_: usize = 0;
    let mut v___x_5362_: usize = 0;
    let mut v___x_5363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5354_ = leanh::lean_ctor_get(v_inst_5351_, 0);
    v_toBind_5355_ = leanh::lean_ctor_get(v_inst_5351_, 1);
    leanh::lean_inc_n(v_toBind_5355_, 2);
    v_toPure_5356_ = leanh::lean_ctor_get(v_toApplicative_5354_, 1);
    v___x_5357_ = leanh::lean_box(0);
    v___x_5358_ = l_Vector_findM_x3f___redArg___closed__0;
    leanh::lean_inc_n(v_toPure_5356_, 2);
    v___f_5359_ = leanh::lean_alloc_closure(
        l_Vector_findM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5359_, 0, v_toPure_5356_);
    v___f_5360_ = leanh::lean_alloc_closure(
        l_Vector_findM_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    leanh::lean_closure_set(v___f_5360_, 0, v___x_5358_);
    leanh::lean_closure_set(v___f_5360_, 1, v_toPure_5356_);
    leanh::lean_closure_set(v___f_5360_, 2, v___x_5357_);
    leanh::lean_closure_set(v___f_5360_, 3, v_f_5352_);
    leanh::lean_closure_set(v___f_5360_, 4, v_toBind_5355_);
    v_sz_5361_ = lean_array_size(v_as_5353_);
    v___x_5362_ = 0usize;
    v___x_5363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_5351_,
        v_as_5353_,
        v___f_5360_,
        v_sz_5361_,
        v___x_5362_,
        v___x_5358_,
    );
    v___x_5364_ = leanh::lean_apply_4(
        v_toBind_5355_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5363_,
        v___f_5359_,
    );
    return v___x_5364_;
}
pub unsafe fn l_Vector_findM_x3f(
    mut v_n_5365_: *mut leanh::LeanObject,
    mut v_00_u03b1_5366_: *mut leanh::LeanObject,
    mut v_m_5367_: *mut leanh::LeanObject,
    mut v_inst_5368_: *mut leanh::LeanObject,
    mut v_f_5369_: *mut leanh::LeanObject,
    mut v_as_5370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5378_: usize = 0;
    let mut v___x_5379_: usize = 0;
    let mut v___x_5380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5371_ = leanh::lean_ctor_get(v_inst_5368_, 0);
    v_toBind_5372_ = leanh::lean_ctor_get(v_inst_5368_, 1);
    leanh::lean_inc_n(v_toBind_5372_, 2);
    v_toPure_5373_ = leanh::lean_ctor_get(v_toApplicative_5371_, 1);
    v___x_5374_ = leanh::lean_box(0);
    v___x_5375_ = l_Vector_findM_x3f___redArg___closed__0;
    leanh::lean_inc_n(v_toPure_5373_, 2);
    v___f_5376_ = leanh::lean_alloc_closure(
        l_Vector_findM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5376_, 0, v_toPure_5373_);
    v___f_5377_ = leanh::lean_alloc_closure(
        l_Vector_findM_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
        8,
        5,
    );
    leanh::lean_closure_set(v___f_5377_, 0, v___x_5375_);
    leanh::lean_closure_set(v___f_5377_, 1, v_toPure_5373_);
    leanh::lean_closure_set(v___f_5377_, 2, v___x_5374_);
    leanh::lean_closure_set(v___f_5377_, 3, v_f_5369_);
    leanh::lean_closure_set(v___f_5377_, 4, v_toBind_5372_);
    v_sz_5378_ = lean_array_size(v_as_5370_);
    v___x_5379_ = 0usize;
    v___x_5380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_5368_,
        v_as_5370_,
        v___f_5377_,
        v_sz_5378_,
        v___x_5379_,
        v___x_5375_,
    );
    v___x_5381_ = leanh::lean_apply_4(
        v_toBind_5372_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5380_,
        v___f_5376_,
    );
    return v___x_5381_;
}
pub unsafe fn l_Vector_findM_x3f___boxed(
    mut v_n_5382_: *mut leanh::LeanObject,
    mut v_00_u03b1_5383_: *mut leanh::LeanObject,
    mut v_m_5384_: *mut leanh::LeanObject,
    mut v_inst_5385_: *mut leanh::LeanObject,
    mut v_f_5386_: *mut leanh::LeanObject,
    mut v_as_5387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5388_ = l_Vector_findM_x3f(
        v_n_5382_,
        v_00_u03b1_5383_,
        v_m_5384_,
        v_inst_5385_,
        v_f_5386_,
        v_as_5387_,
    );
    leanh::lean_dec(v_n_5382_);
    return v_res_5388_;
}
pub unsafe fn l_Vector_findSomeM_x3f___redArg___lam__1(
    mut v___x_5389_: *mut leanh::LeanObject,
    mut v_toPure_5390_: *mut leanh::LeanObject,
    mut v___x_5391_: *mut leanh::LeanObject,
    mut v_____do__lift_5392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_5392_) == 1 {
        let mut v___x_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_5391_);
        v___x_5393_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5393_, 0, v_____do__lift_5392_);
        v___x_5394_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5394_, 0, v___x_5393_);
        leanh::lean_ctor_set(v___x_5394_, 1, v___x_5389_);
        v___x_5395_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5395_, 0, v___x_5394_);
        v___x_5396_ =
            leanh::lean_apply_2(v_toPure_5390_, leanh::lean_box(0), v___x_5395_);
        return v___x_5396_;
    } else {
        let mut v___x_5397_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5398_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_____do__lift_5392_);
        v___x_5397_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5397_, 0, v___x_5391_);
        v___x_5398_ =
            leanh::lean_apply_2(v_toPure_5390_, leanh::lean_box(0), v___x_5397_);
        return v___x_5398_;
    }
}
pub unsafe fn l_Vector_findSomeM_x3f___redArg___lam__0(
    mut v_f_5399_: *mut leanh::LeanObject,
    mut v_toBind_5400_: *mut leanh::LeanObject,
    mut v___f_5401_: *mut leanh::LeanObject,
    mut v_a_5402_: *mut leanh::LeanObject,
    mut v_x_5403_: *mut leanh::LeanObject,
    mut v___y_5404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5405_ = leanh::lean_apply_1(v_f_5399_, v_a_5402_);
    v___x_5406_ = leanh::lean_apply_4(
        v_toBind_5400_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5405_,
        v___f_5401_,
    );
    return v___x_5406_;
}
pub unsafe fn l_Vector_findSomeM_x3f___redArg___lam__0___boxed(
    mut v_f_5407_: *mut leanh::LeanObject,
    mut v_toBind_5408_: *mut leanh::LeanObject,
    mut v___f_5409_: *mut leanh::LeanObject,
    mut v_a_5410_: *mut leanh::LeanObject,
    mut v_x_5411_: *mut leanh::LeanObject,
    mut v___y_5412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5413_ = l_Vector_findSomeM_x3f___redArg___lam__0(
        v_f_5407_,
        v_toBind_5408_,
        v___f_5409_,
        v_a_5410_,
        v_x_5411_,
        v___y_5412_,
    );
    leanh::lean_dec_ref(v___y_5412_);
    return v_res_5413_;
}
pub unsafe fn l_Vector_findSomeM_x3f___redArg(
    mut v_inst_5414_: *mut leanh::LeanObject,
    mut v_f_5415_: *mut leanh::LeanObject,
    mut v_as_5416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_5417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5425_: usize = 0;
    let mut v___x_5426_: usize = 0;
    let mut v___x_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5417_ = leanh::lean_ctor_get(v_inst_5414_, 0);
    v_toBind_5418_ = leanh::lean_ctor_get(v_inst_5414_, 1);
    leanh::lean_inc_n(v_toBind_5418_, 2);
    v_toPure_5419_ = leanh::lean_ctor_get(v_toApplicative_5417_, 1);
    v___x_5420_ = leanh::lean_box(0);
    v___x_5421_ = l_Vector_findM_x3f___redArg___closed__0;
    leanh::lean_inc_n(v_toPure_5419_, 2);
    v___f_5422_ = leanh::lean_alloc_closure(
        l_Vector_findM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5422_, 0, v_toPure_5419_);
    v___f_5423_ = leanh::lean_alloc_closure(
        l_Vector_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_5423_, 0, v___x_5420_);
    leanh::lean_closure_set(v___f_5423_, 1, v_toPure_5419_);
    leanh::lean_closure_set(v___f_5423_, 2, v___x_5421_);
    v___f_5424_ = leanh::lean_alloc_closure(
        l_Vector_findSomeM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_5424_, 0, v_f_5415_);
    leanh::lean_closure_set(v___f_5424_, 1, v_toBind_5418_);
    leanh::lean_closure_set(v___f_5424_, 2, v___f_5423_);
    v_sz_5425_ = lean_array_size(v_as_5416_);
    v___x_5426_ = 0usize;
    v___x_5427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_5414_,
        v_as_5416_,
        v___f_5424_,
        v_sz_5425_,
        v___x_5426_,
        v___x_5421_,
    );
    v___x_5428_ = leanh::lean_apply_4(
        v_toBind_5418_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5427_,
        v___f_5422_,
    );
    return v___x_5428_;
}
pub unsafe fn l_Vector_findSomeM_x3f(
    mut v_m_5429_: *mut leanh::LeanObject,
    mut v_00_u03b1_5430_: *mut leanh::LeanObject,
    mut v_00_u03b2_5431_: *mut leanh::LeanObject,
    mut v_n_5432_: *mut leanh::LeanObject,
    mut v_inst_5433_: *mut leanh::LeanObject,
    mut v_f_5434_: *mut leanh::LeanObject,
    mut v_as_5435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_5436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5444_: usize = 0;
    let mut v___x_5445_: usize = 0;
    let mut v___x_5446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5436_ = leanh::lean_ctor_get(v_inst_5433_, 0);
    v_toBind_5437_ = leanh::lean_ctor_get(v_inst_5433_, 1);
    leanh::lean_inc_n(v_toBind_5437_, 2);
    v_toPure_5438_ = leanh::lean_ctor_get(v_toApplicative_5436_, 1);
    v___x_5439_ = leanh::lean_box(0);
    v___x_5440_ = l_Vector_findM_x3f___redArg___closed__0;
    leanh::lean_inc_n(v_toPure_5438_, 2);
    v___f_5441_ = leanh::lean_alloc_closure(
        l_Vector_findM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5441_, 0, v_toPure_5438_);
    v___f_5442_ = leanh::lean_alloc_closure(
        l_Vector_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_5442_, 0, v___x_5439_);
    leanh::lean_closure_set(v___f_5442_, 1, v_toPure_5438_);
    leanh::lean_closure_set(v___f_5442_, 2, v___x_5440_);
    v___f_5443_ = leanh::lean_alloc_closure(
        l_Vector_findSomeM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_5443_, 0, v_f_5434_);
    leanh::lean_closure_set(v___f_5443_, 1, v_toBind_5437_);
    leanh::lean_closure_set(v___f_5443_, 2, v___f_5442_);
    v_sz_5444_ = lean_array_size(v_as_5435_);
    v___x_5445_ = 0usize;
    v___x_5446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_5433_,
        v_as_5435_,
        v___f_5443_,
        v_sz_5444_,
        v___x_5445_,
        v___x_5440_,
    );
    v___x_5447_ = leanh::lean_apply_4(
        v_toBind_5437_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5446_,
        v___f_5441_,
    );
    return v___x_5447_;
}
pub unsafe fn l_Vector_findSomeM_x3f___boxed(
    mut v_m_5448_: *mut leanh::LeanObject,
    mut v_00_u03b1_5449_: *mut leanh::LeanObject,
    mut v_00_u03b2_5450_: *mut leanh::LeanObject,
    mut v_n_5451_: *mut leanh::LeanObject,
    mut v_inst_5452_: *mut leanh::LeanObject,
    mut v_f_5453_: *mut leanh::LeanObject,
    mut v_as_5454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5455_ = l_Vector_findSomeM_x3f(
        v_m_5448_,
        v_00_u03b1_5449_,
        v_00_u03b2_5450_,
        v_n_5451_,
        v_inst_5452_,
        v_f_5453_,
        v_as_5454_,
    );
    leanh::lean_dec(v_n_5451_);
    return v_res_5455_;
}
pub unsafe fn l_Vector_findRevM_x3f___redArg___lam__0(
    mut v_toPure_5456_: *mut leanh::LeanObject,
    mut v_a_5457_: *mut leanh::LeanObject,
    mut v_____do__lift_5458_: u8,
) -> *mut leanh::LeanObject {
    if v_____do__lift_5458_ == 0 {
        let mut v___x_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_5457_);
        v___x_5459_ = leanh::lean_box(0);
        v___x_5460_ =
            leanh::lean_apply_2(v_toPure_5456_, leanh::lean_box(0), v___x_5459_);
        return v___x_5460_;
    } else {
        let mut v___x_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5461_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5461_, 0, v_a_5457_);
        v___x_5462_ =
            leanh::lean_apply_2(v_toPure_5456_, leanh::lean_box(0), v___x_5461_);
        return v___x_5462_;
    }
}
pub unsafe fn l_Vector_findRevM_x3f___redArg___lam__0___boxed(
    mut v_toPure_5463_: *mut leanh::LeanObject,
    mut v_a_5464_: *mut leanh::LeanObject,
    mut v_____do__lift_5465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_50__boxed_5466_: u8 = 0;
    let mut v_res_5467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_50__boxed_5466_ = (leanh::lean_unbox(v_____do__lift_5465_) as u8);
    v_res_5467_ = l_Vector_findRevM_x3f___redArg___lam__0(
        v_toPure_5463_,
        v_a_5464_,
        v_____do__lift_50__boxed_5466_,
    );
    return v_res_5467_;
}
pub unsafe fn l_Vector_findRevM_x3f___redArg___lam__1(
    mut v_toPure_5468_: *mut leanh::LeanObject,
    mut v_f_5469_: *mut leanh::LeanObject,
    mut v_toBind_5470_: *mut leanh::LeanObject,
    mut v_a_5471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_5471_);
    v___f_5472_ = leanh::lean_alloc_closure(
        l_Vector_findRevM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_5472_, 0, v_toPure_5468_);
    leanh::lean_closure_set(v___f_5472_, 1, v_a_5471_);
    v___x_5473_ = leanh::lean_apply_1(v_f_5469_, v_a_5471_);
    v___x_5474_ = leanh::lean_apply_4(
        v_toBind_5470_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5473_,
        v___f_5472_,
    );
    return v___x_5474_;
}
pub unsafe fn l_Vector_findRevM_x3f___redArg(
    mut v_inst_5475_: *mut leanh::LeanObject,
    mut v_f_5476_: *mut leanh::LeanObject,
    mut v_as_5477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_5478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5478_ = leanh::lean_ctor_get(v_inst_5475_, 0);
    v_toBind_5479_ = leanh::lean_ctor_get(v_inst_5475_, 1);
    v_toPure_5480_ = leanh::lean_ctor_get(v_toApplicative_5478_, 1);
    leanh::lean_inc(v_toBind_5479_);
    leanh::lean_inc(v_toPure_5480_);
    v___f_5481_ = leanh::lean_alloc_closure(
        l_Vector_findRevM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_5481_, 0, v_toPure_5480_);
    leanh::lean_closure_set(v___f_5481_, 1, v_f_5476_);
    leanh::lean_closure_set(v___f_5481_, 2, v_toBind_5479_);
    v___x_5482_ = lean_array_get_size(v_as_5477_);
    v___x_5483_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_5475_,
        v___f_5481_,
        v_as_5477_,
        v___x_5482_,
        leanh::lean_box(0),
    );
    return v___x_5483_;
}
pub unsafe fn l_Vector_findRevM_x3f(
    mut v_n_5484_: *mut leanh::LeanObject,
    mut v_00_u03b1_5485_: *mut leanh::LeanObject,
    mut v_m_5486_: *mut leanh::LeanObject,
    mut v_inst_5487_: *mut leanh::LeanObject,
    mut v_f_5488_: *mut leanh::LeanObject,
    mut v_as_5489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5490_ = leanh::lean_ctor_get(v_inst_5487_, 0);
    v_toBind_5491_ = leanh::lean_ctor_get(v_inst_5487_, 1);
    v_toPure_5492_ = leanh::lean_ctor_get(v_toApplicative_5490_, 1);
    leanh::lean_inc(v_toBind_5491_);
    leanh::lean_inc(v_toPure_5492_);
    v___f_5493_ = leanh::lean_alloc_closure(
        l_Vector_findRevM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_5493_, 0, v_toPure_5492_);
    leanh::lean_closure_set(v___f_5493_, 1, v_f_5488_);
    leanh::lean_closure_set(v___f_5493_, 2, v_toBind_5491_);
    v___x_5494_ = lean_array_get_size(v_as_5489_);
    v___x_5495_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_5487_,
        v___f_5493_,
        v_as_5489_,
        v___x_5494_,
        leanh::lean_box(0),
    );
    return v___x_5495_;
}
pub unsafe fn l_Vector_findRevM_x3f___boxed(
    mut v_n_5496_: *mut leanh::LeanObject,
    mut v_00_u03b1_5497_: *mut leanh::LeanObject,
    mut v_m_5498_: *mut leanh::LeanObject,
    mut v_inst_5499_: *mut leanh::LeanObject,
    mut v_f_5500_: *mut leanh::LeanObject,
    mut v_as_5501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5502_ = l_Vector_findRevM_x3f(
        v_n_5496_,
        v_00_u03b1_5497_,
        v_m_5498_,
        v_inst_5499_,
        v_f_5500_,
        v_as_5501_,
    );
    leanh::lean_dec(v_n_5496_);
    return v_res_5502_;
}
pub unsafe fn l_Vector_findSomeRevM_x3f___redArg(
    mut v_inst_5503_: *mut leanh::LeanObject,
    mut v_f_5504_: *mut leanh::LeanObject,
    mut v_as_5505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5506_ = lean_array_get_size(v_as_5505_);
    v___x_5507_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_5503_,
        v_f_5504_,
        v_as_5505_,
        v___x_5506_,
        leanh::lean_box(0),
    );
    return v___x_5507_;
}
pub unsafe fn l_Vector_findSomeRevM_x3f(
    mut v_m_5508_: *mut leanh::LeanObject,
    mut v_00_u03b1_5509_: *mut leanh::LeanObject,
    mut v_00_u03b2_5510_: *mut leanh::LeanObject,
    mut v_n_5511_: *mut leanh::LeanObject,
    mut v_inst_5512_: *mut leanh::LeanObject,
    mut v_f_5513_: *mut leanh::LeanObject,
    mut v_as_5514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5515_ = lean_array_get_size(v_as_5514_);
    v___x_5516_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_5512_,
        v_f_5513_,
        v_as_5514_,
        v___x_5515_,
        leanh::lean_box(0),
    );
    return v___x_5516_;
}
pub unsafe fn l_Vector_findSomeRevM_x3f___boxed(
    mut v_m_5517_: *mut leanh::LeanObject,
    mut v_00_u03b1_5518_: *mut leanh::LeanObject,
    mut v_00_u03b2_5519_: *mut leanh::LeanObject,
    mut v_n_5520_: *mut leanh::LeanObject,
    mut v_inst_5521_: *mut leanh::LeanObject,
    mut v_f_5522_: *mut leanh::LeanObject,
    mut v_as_5523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5524_ = l_Vector_findSomeRevM_x3f(
        v_m_5517_,
        v_00_u03b1_5518_,
        v_00_u03b2_5519_,
        v_n_5520_,
        v_inst_5521_,
        v_f_5522_,
        v_as_5523_,
    );
    leanh::lean_dec(v_n_5520_);
    return v_res_5524_;
}
pub unsafe fn l_Vector_find_x3f___redArg___lam__0(
    mut v_f_5525_: *mut leanh::LeanObject,
    mut v___x_5526_: *mut leanh::LeanObject,
    mut v___x_5527_: *mut leanh::LeanObject,
    mut v_a_5528_: *mut leanh::LeanObject,
    mut v_x_5529_: *mut leanh::LeanObject,
    mut v___y_5530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: u8 = 0;
    leanh::lean_inc(v_a_5528_);
    v___x_5531_ = leanh::lean_apply_1(v_f_5525_, v_a_5528_);
    v___x_5532_ = (leanh::lean_unbox(v___x_5531_) as u8);
    if v___x_5532_ == 0 {
        let mut v___x_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_5528_);
        v___x_5533_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5533_, 0, v___x_5526_);
        return v___x_5533_;
    } else {
        let mut v___x_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5536_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_5526_);
        v___x_5534_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5534_, 0, v_a_5528_);
        v___x_5535_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5535_, 0, v___x_5534_);
        v___x_5536_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5536_, 0, v___x_5535_);
        leanh::lean_ctor_set(v___x_5536_, 1, v___x_5527_);
        v___x_5537_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5537_, 0, v___x_5536_);
        return v___x_5537_;
    }
}
pub unsafe fn l_Vector_find_x3f___redArg___lam__0___boxed(
    mut v_f_5538_: *mut leanh::LeanObject,
    mut v___x_5539_: *mut leanh::LeanObject,
    mut v___x_5540_: *mut leanh::LeanObject,
    mut v_a_5541_: *mut leanh::LeanObject,
    mut v_x_5542_: *mut leanh::LeanObject,
    mut v___y_5543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5544_ = l_Vector_find_x3f___redArg___lam__0(
        v_f_5538_,
        v___x_5539_,
        v___x_5540_,
        v_a_5541_,
        v_x_5542_,
        v___y_5543_,
    );
    leanh::lean_dec_ref(v___y_5543_);
    return v_res_5544_;
}
pub unsafe fn l_Vector_find_x3f___redArg(
    mut v_f_5545_: *mut leanh::LeanObject,
    mut v_as_5546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5552_: usize = 0;
    let mut v___x_5553_: usize = 0;
    let mut v___x_5554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5547_ = l_Vector_foldl___redArg___closed__9;
    v___x_5548_ = leanh::lean_box(0);
    v___x_5549_ = leanh::lean_box(0);
    v___x_5550_ = l_Vector_findM_x3f___redArg___closed__0;
    v___f_5551_ = leanh::lean_alloc_closure(
        l_Vector_find_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_5551_, 0, v_f_5545_);
    leanh::lean_closure_set(v___f_5551_, 1, v___x_5550_);
    leanh::lean_closure_set(v___f_5551_, 2, v___x_5549_);
    v_sz_5552_ = lean_array_size(v_as_5546_);
    v___x_5553_ = 0usize;
    v___x_5554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5547_,
        v_as_5546_,
        v___f_5551_,
        v_sz_5552_,
        v___x_5553_,
        v___x_5550_,
    );
    v_fst_5555_ = leanh::lean_ctor_get(v___x_5554_, 0);
    leanh::lean_inc(v_fst_5555_);
    leanh::lean_dec(v___x_5554_);
    if leanh::lean_obj_tag(v_fst_5555_) == 0 {
        return v___x_5548_;
    } else {
        let mut v_val_5556_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5556_ = leanh::lean_ctor_get(v_fst_5555_, 0);
        leanh::lean_inc(v_val_5556_);
        leanh::lean_dec_ref_known(v_fst_5555_, 1);
        return v_val_5556_;
    }
}
pub unsafe fn l_Vector_find_x3f(
    mut v_n_5557_: *mut leanh::LeanObject,
    mut v_00_u03b1_5558_: *mut leanh::LeanObject,
    mut v_f_5559_: *mut leanh::LeanObject,
    mut v_as_5560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5566_: usize = 0;
    let mut v___x_5567_: usize = 0;
    let mut v___x_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5561_ = l_Vector_foldl___redArg___closed__9;
    v___x_5562_ = leanh::lean_box(0);
    v___x_5563_ = leanh::lean_box(0);
    v___x_5564_ = l_Vector_findM_x3f___redArg___closed__0;
    v___f_5565_ = leanh::lean_alloc_closure(
        l_Vector_find_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_5565_, 0, v_f_5559_);
    leanh::lean_closure_set(v___f_5565_, 1, v___x_5564_);
    leanh::lean_closure_set(v___f_5565_, 2, v___x_5563_);
    v_sz_5566_ = lean_array_size(v_as_5560_);
    v___x_5567_ = 0usize;
    v___x_5568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5561_,
        v_as_5560_,
        v___f_5565_,
        v_sz_5566_,
        v___x_5567_,
        v___x_5564_,
    );
    v_fst_5569_ = leanh::lean_ctor_get(v___x_5568_, 0);
    leanh::lean_inc(v_fst_5569_);
    leanh::lean_dec(v___x_5568_);
    if leanh::lean_obj_tag(v_fst_5569_) == 0 {
        return v___x_5562_;
    } else {
        let mut v_val_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5570_ = leanh::lean_ctor_get(v_fst_5569_, 0);
        leanh::lean_inc(v_val_5570_);
        leanh::lean_dec_ref_known(v_fst_5569_, 1);
        return v_val_5570_;
    }
}
pub unsafe fn l_Vector_find_x3f___boxed(
    mut v_n_5571_: *mut leanh::LeanObject,
    mut v_00_u03b1_5572_: *mut leanh::LeanObject,
    mut v_f_5573_: *mut leanh::LeanObject,
    mut v_as_5574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5575_ = l_Vector_find_x3f(v_n_5571_, v_00_u03b1_5572_, v_f_5573_, v_as_5574_);
    leanh::lean_dec(v_n_5571_);
    return v_res_5575_;
}
pub unsafe fn l_Vector_findRev_x3f___redArg___lam__0(
    mut v_f_5576_: *mut leanh::LeanObject,
    mut v_a_5577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: u8 = 0;
    leanh::lean_inc(v_a_5577_);
    v___x_5578_ = leanh::lean_apply_1(v_f_5576_, v_a_5577_);
    v___x_5579_ = (leanh::lean_unbox(v___x_5578_) as u8);
    if v___x_5579_ == 0 {
        let mut v___x_5580_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_5577_);
        v___x_5580_ = leanh::lean_box(0);
        return v___x_5580_;
    } else {
        let mut v___x_5581_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5581_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5581_, 0, v_a_5577_);
        return v___x_5581_;
    }
}
pub unsafe fn l_Vector_findRev_x3f___redArg(
    mut v_f_5582_: *mut leanh::LeanObject,
    mut v_as_5583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5584_ = leanh::lean_alloc_closure(
        l_Vector_findRev_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5584_, 0, v_f_5582_);
    v___x_5585_ = l_Vector_foldl___redArg___closed__9;
    v___x_5586_ = lean_array_get_size(v_as_5583_);
    v___x_5587_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5585_,
        v___f_5584_,
        v_as_5583_,
        v___x_5586_,
        leanh::lean_box(0),
    );
    return v___x_5587_;
}
pub unsafe fn l_Vector_findRev_x3f(
    mut v_n_5588_: *mut leanh::LeanObject,
    mut v_00_u03b1_5589_: *mut leanh::LeanObject,
    mut v_f_5590_: *mut leanh::LeanObject,
    mut v_as_5591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5592_ = leanh::lean_alloc_closure(
        l_Vector_findRev_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5592_, 0, v_f_5590_);
    v___x_5593_ = l_Vector_foldl___redArg___closed__9;
    v___x_5594_ = lean_array_get_size(v_as_5591_);
    v___x_5595_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5593_,
        v___f_5592_,
        v_as_5591_,
        v___x_5594_,
        leanh::lean_box(0),
    );
    return v___x_5595_;
}
pub unsafe fn l_Vector_findRev_x3f___boxed(
    mut v_n_5596_: *mut leanh::LeanObject,
    mut v_00_u03b1_5597_: *mut leanh::LeanObject,
    mut v_f_5598_: *mut leanh::LeanObject,
    mut v_as_5599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5600_ = l_Vector_findRev_x3f(v_n_5596_, v_00_u03b1_5597_, v_f_5598_, v_as_5599_);
    leanh::lean_dec(v_n_5596_);
    return v_res_5600_;
}
pub unsafe fn l_Vector_findSome_x3f___redArg___lam__0(
    mut v_f_5601_: *mut leanh::LeanObject,
    mut v___x_5602_: *mut leanh::LeanObject,
    mut v___x_5603_: *mut leanh::LeanObject,
    mut v_a_5604_: *mut leanh::LeanObject,
    mut v_x_5605_: *mut leanh::LeanObject,
    mut v___y_5606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5607_ = leanh::lean_apply_1(v_f_5601_, v_a_5604_);
    if leanh::lean_obj_tag(v___x_5607_) == 1 {
        let mut v___x_5608_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5609_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5610_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_5603_);
        v___x_5608_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5608_, 0, v___x_5607_);
        v___x_5609_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5609_, 0, v___x_5608_);
        leanh::lean_ctor_set(v___x_5609_, 1, v___x_5602_);
        v___x_5610_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5610_, 0, v___x_5609_);
        return v___x_5610_;
    } else {
        let mut v___x_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_5607_);
        v___x_5611_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5611_, 0, v___x_5603_);
        return v___x_5611_;
    }
}
pub unsafe fn l_Vector_findSome_x3f___redArg___lam__0___boxed(
    mut v_f_5612_: *mut leanh::LeanObject,
    mut v___x_5613_: *mut leanh::LeanObject,
    mut v___x_5614_: *mut leanh::LeanObject,
    mut v_a_5615_: *mut leanh::LeanObject,
    mut v_x_5616_: *mut leanh::LeanObject,
    mut v___y_5617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5618_ = l_Vector_findSome_x3f___redArg___lam__0(
        v_f_5612_,
        v___x_5613_,
        v___x_5614_,
        v_a_5615_,
        v_x_5616_,
        v___y_5617_,
    );
    leanh::lean_dec_ref(v___y_5617_);
    return v_res_5618_;
}
pub unsafe fn l_Vector_findSome_x3f___redArg(
    mut v_f_5619_: *mut leanh::LeanObject,
    mut v_as_5620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5626_: usize = 0;
    let mut v___x_5627_: usize = 0;
    let mut v___x_5628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5621_ = l_Vector_foldl___redArg___closed__9;
    v___x_5622_ = leanh::lean_box(0);
    v___x_5623_ = leanh::lean_box(0);
    v___x_5624_ = l_Vector_findM_x3f___redArg___closed__0;
    v___f_5625_ = leanh::lean_alloc_closure(
        l_Vector_findSome_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_5625_, 0, v_f_5619_);
    leanh::lean_closure_set(v___f_5625_, 1, v___x_5623_);
    leanh::lean_closure_set(v___f_5625_, 2, v___x_5624_);
    v_sz_5626_ = lean_array_size(v_as_5620_);
    v___x_5627_ = 0usize;
    v___x_5628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5621_,
        v_as_5620_,
        v___f_5625_,
        v_sz_5626_,
        v___x_5627_,
        v___x_5624_,
    );
    v_fst_5629_ = leanh::lean_ctor_get(v___x_5628_, 0);
    leanh::lean_inc(v_fst_5629_);
    leanh::lean_dec(v___x_5628_);
    if leanh::lean_obj_tag(v_fst_5629_) == 0 {
        return v___x_5622_;
    } else {
        let mut v_val_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5630_ = leanh::lean_ctor_get(v_fst_5629_, 0);
        leanh::lean_inc(v_val_5630_);
        leanh::lean_dec_ref_known(v_fst_5629_, 1);
        return v_val_5630_;
    }
}
pub unsafe fn l_Vector_findSome_x3f(
    mut v_00_u03b1_5631_: *mut leanh::LeanObject,
    mut v_00_u03b2_5632_: *mut leanh::LeanObject,
    mut v_n_5633_: *mut leanh::LeanObject,
    mut v_f_5634_: *mut leanh::LeanObject,
    mut v_as_5635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5641_: usize = 0;
    let mut v___x_5642_: usize = 0;
    let mut v___x_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5636_ = l_Vector_foldl___redArg___closed__9;
    v___x_5637_ = leanh::lean_box(0);
    v___x_5638_ = leanh::lean_box(0);
    v___x_5639_ = l_Vector_findM_x3f___redArg___closed__0;
    v___f_5640_ = leanh::lean_alloc_closure(
        l_Vector_findSome_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_5640_, 0, v_f_5634_);
    leanh::lean_closure_set(v___f_5640_, 1, v___x_5638_);
    leanh::lean_closure_set(v___f_5640_, 2, v___x_5639_);
    v_sz_5641_ = lean_array_size(v_as_5635_);
    v___x_5642_ = 0usize;
    v___x_5643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5636_,
        v_as_5635_,
        v___f_5640_,
        v_sz_5641_,
        v___x_5642_,
        v___x_5639_,
    );
    v_fst_5644_ = leanh::lean_ctor_get(v___x_5643_, 0);
    leanh::lean_inc(v_fst_5644_);
    leanh::lean_dec(v___x_5643_);
    if leanh::lean_obj_tag(v_fst_5644_) == 0 {
        return v___x_5637_;
    } else {
        let mut v_val_5645_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5645_ = leanh::lean_ctor_get(v_fst_5644_, 0);
        leanh::lean_inc(v_val_5645_);
        leanh::lean_dec_ref_known(v_fst_5644_, 1);
        return v_val_5645_;
    }
}
pub unsafe fn l_Vector_findSome_x3f___boxed(
    mut v_00_u03b1_5646_: *mut leanh::LeanObject,
    mut v_00_u03b2_5647_: *mut leanh::LeanObject,
    mut v_n_5648_: *mut leanh::LeanObject,
    mut v_f_5649_: *mut leanh::LeanObject,
    mut v_as_5650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5651_ = l_Vector_findSome_x3f(
        v_00_u03b1_5646_,
        v_00_u03b2_5647_,
        v_n_5648_,
        v_f_5649_,
        v_as_5650_,
    );
    leanh::lean_dec(v_n_5648_);
    return v_res_5651_;
}
pub unsafe fn l_Vector_findSomeRev_x3f___redArg___lam__0(
    mut v_f_5652_: *mut leanh::LeanObject,
    mut v_x_5653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5654_ = leanh::lean_apply_1(v_f_5652_, v_x_5653_);
    return v___x_5654_;
}
pub unsafe fn l_Vector_findSomeRev_x3f___redArg(
    mut v_f_5655_: *mut leanh::LeanObject,
    mut v_as_5656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5657_ = leanh::lean_alloc_closure(
        l_Vector_findSomeRev_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5657_, 0, v_f_5655_);
    v___x_5658_ = l_Vector_foldl___redArg___closed__9;
    v___x_5659_ = lean_array_get_size(v_as_5656_);
    v___x_5660_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5658_,
        v___f_5657_,
        v_as_5656_,
        v___x_5659_,
        leanh::lean_box(0),
    );
    return v___x_5660_;
}
pub unsafe fn l_Vector_findSomeRev_x3f(
    mut v_00_u03b1_5661_: *mut leanh::LeanObject,
    mut v_00_u03b2_5662_: *mut leanh::LeanObject,
    mut v_n_5663_: *mut leanh::LeanObject,
    mut v_f_5664_: *mut leanh::LeanObject,
    mut v_as_5665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5666_ = leanh::lean_alloc_closure(
        l_Vector_findSomeRev_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5666_, 0, v_f_5664_);
    v___x_5667_ = l_Vector_foldl___redArg___closed__9;
    v___x_5668_ = lean_array_get_size(v_as_5665_);
    v___x_5669_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5667_,
        v___f_5666_,
        v_as_5665_,
        v___x_5668_,
        leanh::lean_box(0),
    );
    return v___x_5669_;
}
pub unsafe fn l_Vector_findSomeRev_x3f___boxed(
    mut v_00_u03b1_5670_: *mut leanh::LeanObject,
    mut v_00_u03b2_5671_: *mut leanh::LeanObject,
    mut v_n_5672_: *mut leanh::LeanObject,
    mut v_f_5673_: *mut leanh::LeanObject,
    mut v_as_5674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5675_ = l_Vector_findSomeRev_x3f(
        v_00_u03b1_5670_,
        v_00_u03b2_5671_,
        v_n_5672_,
        v_f_5673_,
        v_as_5674_,
    );
    leanh::lean_dec(v_n_5672_);
    return v_res_5675_;
}
pub unsafe fn l_Vector_isPrefixOf___redArg(
    mut v_inst_5676_: *mut leanh::LeanObject,
    mut v_xs_5677_: *mut leanh::LeanObject,
    mut v_ys_5678_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5679_: u8 = 0;
    v___x_5679_ = l_Array_isPrefixOf___redArg(v_inst_5676_, v_xs_5677_, v_ys_5678_);
    return v___x_5679_;
}
pub unsafe fn l_Vector_isPrefixOf___redArg___boxed(
    mut v_inst_5680_: *mut leanh::LeanObject,
    mut v_xs_5681_: *mut leanh::LeanObject,
    mut v_ys_5682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5683_: u8 = 0;
    let mut v_r_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5683_ = l_Vector_isPrefixOf___redArg(v_inst_5680_, v_xs_5681_, v_ys_5682_);
    leanh::lean_dec_ref(v_ys_5682_);
    leanh::lean_dec_ref(v_xs_5681_);
    v_r_5684_ = leanh::lean_box((v_res_5683_) as usize);
    return v_r_5684_;
}
pub unsafe fn l_Vector_isPrefixOf(
    mut v_00_u03b1_5685_: *mut leanh::LeanObject,
    mut v_m_5686_: *mut leanh::LeanObject,
    mut v_n_5687_: *mut leanh::LeanObject,
    mut v_inst_5688_: *mut leanh::LeanObject,
    mut v_xs_5689_: *mut leanh::LeanObject,
    mut v_ys_5690_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5691_: u8 = 0;
    v___x_5691_ = l_Array_isPrefixOf___redArg(v_inst_5688_, v_xs_5689_, v_ys_5690_);
    return v___x_5691_;
}
pub unsafe fn l_Vector_isPrefixOf___boxed(
    mut v_00_u03b1_5692_: *mut leanh::LeanObject,
    mut v_m_5693_: *mut leanh::LeanObject,
    mut v_n_5694_: *mut leanh::LeanObject,
    mut v_inst_5695_: *mut leanh::LeanObject,
    mut v_xs_5696_: *mut leanh::LeanObject,
    mut v_ys_5697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5698_: u8 = 0;
    let mut v_r_5699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5698_ = l_Vector_isPrefixOf(
        v_00_u03b1_5692_,
        v_m_5693_,
        v_n_5694_,
        v_inst_5695_,
        v_xs_5696_,
        v_ys_5697_,
    );
    leanh::lean_dec_ref(v_ys_5697_);
    leanh::lean_dec_ref(v_xs_5696_);
    leanh::lean_dec(v_n_5694_);
    leanh::lean_dec(v_m_5693_);
    v_r_5699_ = leanh::lean_box((v_res_5698_) as usize);
    return v_r_5699_;
}
pub unsafe fn l_Vector_anyM___redArg(
    mut v_inst_5700_: *mut leanh::LeanObject,
    mut v_p_5701_: *mut leanh::LeanObject,
    mut v_xs_5702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: u8 = 0;
    v___x_5703_ = leanh::lean_unsigned_to_nat(0);
    v___x_5704_ = lean_array_get_size(v_xs_5702_);
    v___x_5705_ = lean_nat_dec_lt(v___x_5703_, v___x_5704_);
    if v___x_5705_ == 0 {
        let mut v_toApplicative_5706_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_5707_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_5702_);
        leanh::lean_dec(v_p_5701_);
        v_toApplicative_5706_ = leanh::lean_ctor_get(v_inst_5700_, 0);
        leanh::lean_inc_ref(v_toApplicative_5706_);
        leanh::lean_dec_ref(v_inst_5700_);
        v_toPure_5707_ = leanh::lean_ctor_get(v_toApplicative_5706_, 1);
        leanh::lean_inc(v_toPure_5707_);
        leanh::lean_dec_ref(v_toApplicative_5706_);
        v___x_5708_ = leanh::lean_box((v___x_5705_) as usize);
        v___x_5709_ =
            leanh::lean_apply_2(v_toPure_5707_, leanh::lean_box(0), v___x_5708_);
        return v___x_5709_;
    } else {
        if v___x_5705_ == 0 {
            let mut v_toApplicative_5710_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5712_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5713_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_xs_5702_);
            leanh::lean_dec(v_p_5701_);
            v_toApplicative_5710_ = leanh::lean_ctor_get(v_inst_5700_, 0);
            leanh::lean_inc_ref(v_toApplicative_5710_);
            leanh::lean_dec_ref(v_inst_5700_);
            v_toPure_5711_ = leanh::lean_ctor_get(v_toApplicative_5710_, 1);
            leanh::lean_inc(v_toPure_5711_);
            leanh::lean_dec_ref(v_toApplicative_5710_);
            v___x_5712_ = leanh::lean_box((v___x_5705_) as usize);
            v___x_5713_ =
                leanh::lean_apply_2(v_toPure_5711_, leanh::lean_box(0), v___x_5712_);
            return v___x_5713_;
        } else {
            let mut v___x_5714_: usize = 0;
            let mut v___x_5715_: usize = 0;
            let mut v___x_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5714_ = 0usize;
            v___x_5715_ = lean_usize_of_nat(v___x_5704_);
            v___x_5716_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_5700_,
                v_p_5701_,
                v_xs_5702_,
                v___x_5714_,
                v___x_5715_,
            );
            return v___x_5716_;
        }
    }
}
pub unsafe fn l_Vector_anyM(
    mut v_m_5717_: *mut leanh::LeanObject,
    mut v_00_u03b1_5718_: *mut leanh::LeanObject,
    mut v_n_5719_: *mut leanh::LeanObject,
    mut v_inst_5720_: *mut leanh::LeanObject,
    mut v_p_5721_: *mut leanh::LeanObject,
    mut v_xs_5722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: u8 = 0;
    v___x_5723_ = leanh::lean_unsigned_to_nat(0);
    v___x_5724_ = lean_array_get_size(v_xs_5722_);
    v___x_5725_ = lean_nat_dec_lt(v___x_5723_, v___x_5724_);
    if v___x_5725_ == 0 {
        let mut v_toApplicative_5726_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_5727_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5728_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5729_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_5722_);
        leanh::lean_dec(v_p_5721_);
        v_toApplicative_5726_ = leanh::lean_ctor_get(v_inst_5720_, 0);
        leanh::lean_inc_ref(v_toApplicative_5726_);
        leanh::lean_dec_ref(v_inst_5720_);
        v_toPure_5727_ = leanh::lean_ctor_get(v_toApplicative_5726_, 1);
        leanh::lean_inc(v_toPure_5727_);
        leanh::lean_dec_ref(v_toApplicative_5726_);
        v___x_5728_ = leanh::lean_box((v___x_5725_) as usize);
        v___x_5729_ =
            leanh::lean_apply_2(v_toPure_5727_, leanh::lean_box(0), v___x_5728_);
        return v___x_5729_;
    } else {
        if v___x_5725_ == 0 {
            let mut v_toApplicative_5730_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_5731_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5732_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5733_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_xs_5722_);
            leanh::lean_dec(v_p_5721_);
            v_toApplicative_5730_ = leanh::lean_ctor_get(v_inst_5720_, 0);
            leanh::lean_inc_ref(v_toApplicative_5730_);
            leanh::lean_dec_ref(v_inst_5720_);
            v_toPure_5731_ = leanh::lean_ctor_get(v_toApplicative_5730_, 1);
            leanh::lean_inc(v_toPure_5731_);
            leanh::lean_dec_ref(v_toApplicative_5730_);
            v___x_5732_ = leanh::lean_box((v___x_5725_) as usize);
            v___x_5733_ =
                leanh::lean_apply_2(v_toPure_5731_, leanh::lean_box(0), v___x_5732_);
            return v___x_5733_;
        } else {
            let mut v___x_5734_: usize = 0;
            let mut v___x_5735_: usize = 0;
            let mut v___x_5736_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5734_ = 0usize;
            v___x_5735_ = lean_usize_of_nat(v___x_5724_);
            v___x_5736_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_5720_,
                v_p_5721_,
                v_xs_5722_,
                v___x_5734_,
                v___x_5735_,
            );
            return v___x_5736_;
        }
    }
}
pub unsafe fn l_Vector_anyM___boxed(
    mut v_m_5737_: *mut leanh::LeanObject,
    mut v_00_u03b1_5738_: *mut leanh::LeanObject,
    mut v_n_5739_: *mut leanh::LeanObject,
    mut v_inst_5740_: *mut leanh::LeanObject,
    mut v_p_5741_: *mut leanh::LeanObject,
    mut v_xs_5742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5743_ = l_Vector_anyM(
        v_m_5737_,
        v_00_u03b1_5738_,
        v_n_5739_,
        v_inst_5740_,
        v_p_5741_,
        v_xs_5742_,
    );
    leanh::lean_dec(v_n_5739_);
    return v_res_5743_;
}
pub unsafe fn l_Vector_allM___redArg___lam__0(
    mut v_toPure_5744_: *mut leanh::LeanObject,
    mut v_____do__lift_5745_: u8,
) -> *mut leanh::LeanObject {
    if v_____do__lift_5745_ == 0 {
        let mut v___x_5746_: u8 = 0;
        let mut v___x_5747_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5748_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5746_ = 1;
        v___x_5747_ = leanh::lean_box((v___x_5746_) as usize);
        v___x_5748_ =
            leanh::lean_apply_2(v_toPure_5744_, leanh::lean_box(0), v___x_5747_);
        return v___x_5748_;
    } else {
        let mut v___x_5749_: u8 = 0;
        let mut v___x_5750_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5749_ = 0;
        v___x_5750_ = leanh::lean_box((v___x_5749_) as usize);
        v___x_5751_ =
            leanh::lean_apply_2(v_toPure_5744_, leanh::lean_box(0), v___x_5750_);
        return v___x_5751_;
    }
}
pub unsafe fn l_Vector_allM___redArg___lam__0___boxed(
    mut v_toPure_5752_: *mut leanh::LeanObject,
    mut v_____do__lift_5753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_117__boxed_5754_: u8 = 0;
    let mut v_res_5755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_117__boxed_5754_ = (leanh::lean_unbox(v_____do__lift_5753_) as u8);
    v_res_5755_ = l_Vector_allM___redArg___lam__0(v_toPure_5752_, v_____do__lift_117__boxed_5754_);
    return v_res_5755_;
}
pub unsafe fn l_Vector_allM___redArg___lam__1(
    mut v_toPure_5756_: *mut leanh::LeanObject,
    mut v___x_5757_: u8,
    mut v_____do__lift_5758_: u8,
) -> *mut leanh::LeanObject {
    if v_____do__lift_5758_ == 0 {
        let mut v___x_5759_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5759_ = leanh::lean_box((v___x_5757_) as usize);
        v___x_5760_ =
            leanh::lean_apply_2(v_toPure_5756_, leanh::lean_box(0), v___x_5759_);
        return v___x_5760_;
    } else {
        let mut v___x_5761_: u8 = 0;
        let mut v___x_5762_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5763_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5761_ = 0;
        v___x_5762_ = leanh::lean_box((v___x_5761_) as usize);
        v___x_5763_ =
            leanh::lean_apply_2(v_toPure_5756_, leanh::lean_box(0), v___x_5762_);
        return v___x_5763_;
    }
}
pub unsafe fn l_Vector_allM___redArg___lam__1___boxed(
    mut v_toPure_5764_: *mut leanh::LeanObject,
    mut v___x_5765_: *mut leanh::LeanObject,
    mut v_____do__lift_5766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_132__boxed_5767_: u8 = 0;
    let mut v_____do__lift_133__boxed_5768_: u8 = 0;
    let mut v_res_5769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_132__boxed_5767_ = (leanh::lean_unbox(v___x_5765_) as u8);
    v_____do__lift_133__boxed_5768_ = (leanh::lean_unbox(v_____do__lift_5766_) as u8);
    v_res_5769_ = l_Vector_allM___redArg___lam__1(
        v_toPure_5764_,
        v___x_132__boxed_5767_,
        v_____do__lift_133__boxed_5768_,
    );
    return v_res_5769_;
}
pub unsafe fn l_Vector_allM___redArg___lam__2(
    mut v_p_5770_: *mut leanh::LeanObject,
    mut v_toBind_5771_: *mut leanh::LeanObject,
    mut v___f_5772_: *mut leanh::LeanObject,
    mut v_v_5773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5774_ = leanh::lean_apply_1(v_p_5770_, v_v_5773_);
    v___x_5775_ = leanh::lean_apply_4(
        v_toBind_5771_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5774_,
        v___f_5772_,
    );
    return v___x_5775_;
}
pub unsafe fn l_Vector_allM___redArg(
    mut v_inst_5776_: *mut leanh::LeanObject,
    mut v_p_5777_: *mut leanh::LeanObject,
    mut v_xs_5778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: u8 = 0;
    v_toApplicative_5779_ = leanh::lean_ctor_get(v_inst_5776_, 0);
    v_toBind_5780_ = leanh::lean_ctor_get(v_inst_5776_, 1);
    leanh::lean_inc(v_toBind_5780_);
    v_toPure_5781_ = leanh::lean_ctor_get(v_toApplicative_5779_, 1);
    v___x_5782_ = leanh::lean_unsigned_to_nat(0);
    v___x_5783_ = lean_array_get_size(v_xs_5778_);
    leanh::lean_inc(v_toPure_5781_);
    v___f_5784_ = leanh::lean_alloc_closure(
        l_Vector_allM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5784_, 0, v_toPure_5781_);
    v___x_5785_ = lean_nat_dec_lt(v___x_5782_, v___x_5783_);
    if v___x_5785_ == 0 {
        let mut v___x_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5788_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_toPure_5781_);
        leanh::lean_dec_ref(v_xs_5778_);
        leanh::lean_dec(v_p_5777_);
        leanh::lean_dec_ref(v_inst_5776_);
        v___x_5786_ = leanh::lean_box((v___x_5785_) as usize);
        v___x_5787_ =
            leanh::lean_apply_2(v_toPure_5781_, leanh::lean_box(0), v___x_5786_);
        v___x_5788_ = leanh::lean_apply_4(
            v_toBind_5780_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_5787_,
            v___f_5784_,
        );
        return v___x_5788_;
    } else {
        if v___x_5785_ == 0 {
            let mut v___x_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5791_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_toPure_5781_);
            leanh::lean_dec_ref(v_xs_5778_);
            leanh::lean_dec(v_p_5777_);
            leanh::lean_dec_ref(v_inst_5776_);
            v___x_5789_ = leanh::lean_box((v___x_5785_) as usize);
            v___x_5790_ =
                leanh::lean_apply_2(v_toPure_5781_, leanh::lean_box(0), v___x_5789_);
            v___x_5791_ = leanh::lean_apply_4(
                v_toBind_5780_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_5790_,
                v___f_5784_,
            );
            return v___x_5791_;
        } else {
            let mut v___x_5792_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5795_: usize = 0;
            let mut v___x_5796_: usize = 0;
            let mut v___x_5797_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5792_ = leanh::lean_box((v___x_5785_) as usize);
            leanh::lean_inc(v_toPure_5781_);
            v___f_5793_ = leanh::lean_alloc_closure(
                l_Vector_allM___redArg___lam__1___boxed as *mut core::ffi::c_void,
                3,
                2,
            );
            leanh::lean_closure_set(v___f_5793_, 0, v_toPure_5781_);
            leanh::lean_closure_set(v___f_5793_, 1, v___x_5792_);
            leanh::lean_inc(v_toBind_5780_);
            v___f_5794_ = leanh::lean_alloc_closure(
                l_Vector_allM___redArg___lam__2 as *mut core::ffi::c_void,
                4,
                3,
            );
            leanh::lean_closure_set(v___f_5794_, 0, v_p_5777_);
            leanh::lean_closure_set(v___f_5794_, 1, v_toBind_5780_);
            leanh::lean_closure_set(v___f_5794_, 2, v___f_5793_);
            v___x_5795_ = 0usize;
            v___x_5796_ = lean_usize_of_nat(v___x_5783_);
            v___x_5797_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_5776_,
                v___f_5794_,
                v_xs_5778_,
                v___x_5795_,
                v___x_5796_,
            );
            v___x_5798_ = leanh::lean_apply_4(
                v_toBind_5780_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_5797_,
                v___f_5784_,
            );
            return v___x_5798_;
        }
    }
}
pub unsafe fn l_Vector_allM(
    mut v_m_5799_: *mut leanh::LeanObject,
    mut v_00_u03b1_5800_: *mut leanh::LeanObject,
    mut v_n_5801_: *mut leanh::LeanObject,
    mut v_inst_5802_: *mut leanh::LeanObject,
    mut v_p_5803_: *mut leanh::LeanObject,
    mut v_xs_5804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: u8 = 0;
    v_toApplicative_5805_ = leanh::lean_ctor_get(v_inst_5802_, 0);
    v_toBind_5806_ = leanh::lean_ctor_get(v_inst_5802_, 1);
    leanh::lean_inc(v_toBind_5806_);
    v_toPure_5807_ = leanh::lean_ctor_get(v_toApplicative_5805_, 1);
    v___x_5808_ = leanh::lean_unsigned_to_nat(0);
    v___x_5809_ = lean_array_get_size(v_xs_5804_);
    leanh::lean_inc(v_toPure_5807_);
    v___f_5810_ = leanh::lean_alloc_closure(
        l_Vector_allM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5810_, 0, v_toPure_5807_);
    v___x_5811_ = lean_nat_dec_lt(v___x_5808_, v___x_5809_);
    if v___x_5811_ == 0 {
        let mut v___x_5812_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5814_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_toPure_5807_);
        leanh::lean_dec_ref(v_xs_5804_);
        leanh::lean_dec(v_p_5803_);
        leanh::lean_dec_ref(v_inst_5802_);
        v___x_5812_ = leanh::lean_box((v___x_5811_) as usize);
        v___x_5813_ =
            leanh::lean_apply_2(v_toPure_5807_, leanh::lean_box(0), v___x_5812_);
        v___x_5814_ = leanh::lean_apply_4(
            v_toBind_5806_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_5813_,
            v___f_5810_,
        );
        return v___x_5814_;
    } else {
        if v___x_5811_ == 0 {
            let mut v___x_5815_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_toPure_5807_);
            leanh::lean_dec_ref(v_xs_5804_);
            leanh::lean_dec(v_p_5803_);
            leanh::lean_dec_ref(v_inst_5802_);
            v___x_5815_ = leanh::lean_box((v___x_5811_) as usize);
            v___x_5816_ =
                leanh::lean_apply_2(v_toPure_5807_, leanh::lean_box(0), v___x_5815_);
            v___x_5817_ = leanh::lean_apply_4(
                v_toBind_5806_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_5816_,
                v___f_5810_,
            );
            return v___x_5817_;
        } else {
            let mut v___x_5818_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5821_: usize = 0;
            let mut v___x_5822_: usize = 0;
            let mut v___x_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5824_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5818_ = leanh::lean_box((v___x_5811_) as usize);
            leanh::lean_inc(v_toPure_5807_);
            v___f_5819_ = leanh::lean_alloc_closure(
                l_Vector_allM___redArg___lam__1___boxed as *mut core::ffi::c_void,
                3,
                2,
            );
            leanh::lean_closure_set(v___f_5819_, 0, v_toPure_5807_);
            leanh::lean_closure_set(v___f_5819_, 1, v___x_5818_);
            leanh::lean_inc(v_toBind_5806_);
            v___f_5820_ = leanh::lean_alloc_closure(
                l_Vector_allM___redArg___lam__2 as *mut core::ffi::c_void,
                4,
                3,
            );
            leanh::lean_closure_set(v___f_5820_, 0, v_p_5803_);
            leanh::lean_closure_set(v___f_5820_, 1, v_toBind_5806_);
            leanh::lean_closure_set(v___f_5820_, 2, v___f_5819_);
            v___x_5821_ = 0usize;
            v___x_5822_ = lean_usize_of_nat(v___x_5809_);
            v___x_5823_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_5802_,
                v___f_5820_,
                v_xs_5804_,
                v___x_5821_,
                v___x_5822_,
            );
            v___x_5824_ = leanh::lean_apply_4(
                v_toBind_5806_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_5823_,
                v___f_5810_,
            );
            return v___x_5824_;
        }
    }
}
pub unsafe fn l_Vector_allM___boxed(
    mut v_m_5825_: *mut leanh::LeanObject,
    mut v_00_u03b1_5826_: *mut leanh::LeanObject,
    mut v_n_5827_: *mut leanh::LeanObject,
    mut v_inst_5828_: *mut leanh::LeanObject,
    mut v_p_5829_: *mut leanh::LeanObject,
    mut v_xs_5830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5831_ = l_Vector_allM(
        v_m_5825_,
        v_00_u03b1_5826_,
        v_n_5827_,
        v_inst_5828_,
        v_p_5829_,
        v_xs_5830_,
    );
    leanh::lean_dec(v_n_5827_);
    return v_res_5831_;
}
pub unsafe fn l_Vector_any___redArg___lam__0(
    mut v_p_5832_: *mut leanh::LeanObject,
    mut v_x_5833_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: u8 = 0;
    v___x_5834_ = leanh::lean_apply_1(v_p_5832_, v_x_5833_);
    v___x_5835_ = (leanh::lean_unbox(v___x_5834_) as u8);
    return v___x_5835_;
}
pub unsafe fn l_Vector_any___redArg___lam__0___boxed(
    mut v_p_5836_: *mut leanh::LeanObject,
    mut v_x_5837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5838_: u8 = 0;
    let mut v_r_5839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5838_ = l_Vector_any___redArg___lam__0(v_p_5836_, v_x_5837_);
    v_r_5839_ = leanh::lean_box((v_res_5838_) as usize);
    return v_r_5839_;
}
pub unsafe fn l_Vector_any___redArg(
    mut v_xs_5840_: *mut leanh::LeanObject,
    mut v_p_5841_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: u8 = 0;
    v___x_5842_ = leanh::lean_unsigned_to_nat(0);
    v___x_5843_ = lean_array_get_size(v_xs_5840_);
    v___x_5844_ = l_Vector_foldl___redArg___closed__9;
    v___x_5845_ = lean_nat_dec_lt(v___x_5842_, v___x_5843_);
    if v___x_5845_ == 0 {
        leanh::lean_dec_ref(v_p_5841_);
        leanh::lean_dec_ref(v_xs_5840_);
        return v___x_5845_;
    } else {
        if v___x_5845_ == 0 {
            leanh::lean_dec_ref(v_p_5841_);
            leanh::lean_dec_ref(v_xs_5840_);
            return v___x_5845_;
        } else {
            let mut v___f_5846_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5847_: usize = 0;
            let mut v___x_5848_: usize = 0;
            let mut v___x_5849_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5850_: u8 = 0;
            v___f_5846_ = leanh::lean_alloc_closure(
                l_Vector_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            leanh::lean_closure_set(v___f_5846_, 0, v_p_5841_);
            v___x_5847_ = 0usize;
            v___x_5848_ = lean_usize_of_nat(v___x_5843_);
            v___x_5849_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_5844_,
                v___f_5846_,
                v_xs_5840_,
                v___x_5847_,
                v___x_5848_,
            );
            v___x_5850_ = (leanh::lean_unbox(v___x_5849_) as u8);
            leanh::lean_dec(v___x_5849_);
            return v___x_5850_;
        }
    }
}
pub unsafe fn l_Vector_any___redArg___boxed(
    mut v_xs_5851_: *mut leanh::LeanObject,
    mut v_p_5852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5853_: u8 = 0;
    let mut v_r_5854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5853_ = l_Vector_any___redArg(v_xs_5851_, v_p_5852_);
    v_r_5854_ = leanh::lean_box((v_res_5853_) as usize);
    return v_r_5854_;
}
pub unsafe fn l_Vector_any(
    mut v_00_u03b1_5855_: *mut leanh::LeanObject,
    mut v_n_5856_: *mut leanh::LeanObject,
    mut v_xs_5857_: *mut leanh::LeanObject,
    mut v_p_5858_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: u8 = 0;
    v___x_5859_ = leanh::lean_unsigned_to_nat(0);
    v___x_5860_ = lean_array_get_size(v_xs_5857_);
    v___x_5861_ = l_Vector_foldl___redArg___closed__9;
    v___x_5862_ = lean_nat_dec_lt(v___x_5859_, v___x_5860_);
    if v___x_5862_ == 0 {
        leanh::lean_dec_ref(v_p_5858_);
        leanh::lean_dec_ref(v_xs_5857_);
        return v___x_5862_;
    } else {
        if v___x_5862_ == 0 {
            leanh::lean_dec_ref(v_p_5858_);
            leanh::lean_dec_ref(v_xs_5857_);
            return v___x_5862_;
        } else {
            let mut v___f_5863_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5864_: usize = 0;
            let mut v___x_5865_: usize = 0;
            let mut v___x_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5867_: u8 = 0;
            v___f_5863_ = leanh::lean_alloc_closure(
                l_Vector_any___redArg___lam__0___boxed as *mut core::ffi::c_void,
                2,
                1,
            );
            leanh::lean_closure_set(v___f_5863_, 0, v_p_5858_);
            v___x_5864_ = 0usize;
            v___x_5865_ = lean_usize_of_nat(v___x_5860_);
            v___x_5866_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_5861_,
                v___f_5863_,
                v_xs_5857_,
                v___x_5864_,
                v___x_5865_,
            );
            v___x_5867_ = (leanh::lean_unbox(v___x_5866_) as u8);
            leanh::lean_dec(v___x_5866_);
            return v___x_5867_;
        }
    }
}
pub unsafe fn l_Vector_any___boxed(
    mut v_00_u03b1_5868_: *mut leanh::LeanObject,
    mut v_n_5869_: *mut leanh::LeanObject,
    mut v_xs_5870_: *mut leanh::LeanObject,
    mut v_p_5871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5872_: u8 = 0;
    let mut v_r_5873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5872_ = l_Vector_any(v_00_u03b1_5868_, v_n_5869_, v_xs_5870_, v_p_5871_);
    leanh::lean_dec(v_n_5869_);
    v_r_5873_ = leanh::lean_box((v_res_5872_) as usize);
    return v_r_5873_;
}
pub unsafe fn l_Vector_all___redArg___lam__0(
    mut v_p_5874_: *mut leanh::LeanObject,
    mut v___x_5875_: u8,
    mut v_v_5876_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: u8 = 0;
    v___x_5877_ = leanh::lean_apply_1(v_p_5874_, v_v_5876_);
    v___x_5878_ = (leanh::lean_unbox(v___x_5877_) as u8);
    if v___x_5878_ == 0 {
        return v___x_5875_;
    } else {
        let mut v___x_5879_: u8 = 0;
        v___x_5879_ = 0;
        return v___x_5879_;
    }
}
pub unsafe fn l_Vector_all___redArg___lam__0___boxed(
    mut v_p_5880_: *mut leanh::LeanObject,
    mut v___x_5881_: *mut leanh::LeanObject,
    mut v_v_5882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_79__boxed_5883_: u8 = 0;
    let mut v_res_5884_: u8 = 0;
    let mut v_r_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_79__boxed_5883_ = (leanh::lean_unbox(v___x_5881_) as u8);
    v_res_5884_ = l_Vector_all___redArg___lam__0(v_p_5880_, v___x_79__boxed_5883_, v_v_5882_);
    v_r_5885_ = leanh::lean_box((v_res_5884_) as usize);
    return v_r_5885_;
}
pub unsafe fn l_Vector_all___redArg(
    mut v_xs_5886_: *mut leanh::LeanObject,
    mut v_p_5887_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: u8 = 0;
    v___x_5888_ = leanh::lean_unsigned_to_nat(0);
    v___x_5889_ = lean_array_get_size(v_xs_5886_);
    v___x_5890_ = l_Vector_foldl___redArg___closed__9;
    v___x_5891_ = lean_nat_dec_lt(v___x_5888_, v___x_5889_);
    if v___x_5891_ == 0 {
        let mut v___x_5892_: u8 = 0;
        leanh::lean_dec_ref(v_p_5887_);
        leanh::lean_dec_ref(v_xs_5886_);
        v___x_5892_ = 1;
        return v___x_5892_;
    } else {
        if v___x_5891_ == 0 {
            leanh::lean_dec_ref(v_p_5887_);
            leanh::lean_dec_ref(v_xs_5886_);
            return v___x_5891_;
        } else {
            let mut v___x_5893_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5894_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5895_: usize = 0;
            let mut v___x_5896_: usize = 0;
            let mut v___x_5897_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5898_: u8 = 0;
            v___x_5893_ = leanh::lean_box((v___x_5891_) as usize);
            v___f_5894_ = leanh::lean_alloc_closure(
                l_Vector_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                3,
                2,
            );
            leanh::lean_closure_set(v___f_5894_, 0, v_p_5887_);
            leanh::lean_closure_set(v___f_5894_, 1, v___x_5893_);
            v___x_5895_ = 0usize;
            v___x_5896_ = lean_usize_of_nat(v___x_5889_);
            v___x_5897_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_5890_,
                v___f_5894_,
                v_xs_5886_,
                v___x_5895_,
                v___x_5896_,
            );
            v___x_5898_ = (leanh::lean_unbox(v___x_5897_) as u8);
            leanh::lean_dec(v___x_5897_);
            if v___x_5898_ == 0 {
                return v___x_5891_;
            } else {
                let mut v___x_5899_: u8 = 0;
                v___x_5899_ = 0;
                return v___x_5899_;
            }
        }
    }
}
pub unsafe fn l_Vector_all___redArg___boxed(
    mut v_xs_5900_: *mut leanh::LeanObject,
    mut v_p_5901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5902_: u8 = 0;
    let mut v_r_5903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5902_ = l_Vector_all___redArg(v_xs_5900_, v_p_5901_);
    v_r_5903_ = leanh::lean_box((v_res_5902_) as usize);
    return v_r_5903_;
}
pub unsafe fn l_Vector_all(
    mut v_00_u03b1_5904_: *mut leanh::LeanObject,
    mut v_n_5905_: *mut leanh::LeanObject,
    mut v_xs_5906_: *mut leanh::LeanObject,
    mut v_p_5907_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: u8 = 0;
    v___x_5908_ = leanh::lean_unsigned_to_nat(0);
    v___x_5909_ = lean_array_get_size(v_xs_5906_);
    v___x_5910_ = l_Vector_foldl___redArg___closed__9;
    v___x_5911_ = lean_nat_dec_lt(v___x_5908_, v___x_5909_);
    if v___x_5911_ == 0 {
        let mut v___x_5912_: u8 = 0;
        leanh::lean_dec_ref(v_p_5907_);
        leanh::lean_dec_ref(v_xs_5906_);
        v___x_5912_ = 1;
        return v___x_5912_;
    } else {
        if v___x_5911_ == 0 {
            leanh::lean_dec_ref(v_p_5907_);
            leanh::lean_dec_ref(v_xs_5906_);
            return v___x_5911_;
        } else {
            let mut v___x_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5914_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5915_: usize = 0;
            let mut v___x_5916_: usize = 0;
            let mut v___x_5917_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5918_: u8 = 0;
            v___x_5913_ = leanh::lean_box((v___x_5911_) as usize);
            v___f_5914_ = leanh::lean_alloc_closure(
                l_Vector_all___redArg___lam__0___boxed as *mut core::ffi::c_void,
                3,
                2,
            );
            leanh::lean_closure_set(v___f_5914_, 0, v_p_5907_);
            leanh::lean_closure_set(v___f_5914_, 1, v___x_5913_);
            v___x_5915_ = 0usize;
            v___x_5916_ = lean_usize_of_nat(v___x_5909_);
            v___x_5917_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_5910_,
                v___f_5914_,
                v_xs_5906_,
                v___x_5915_,
                v___x_5916_,
            );
            v___x_5918_ = (leanh::lean_unbox(v___x_5917_) as u8);
            leanh::lean_dec(v___x_5917_);
            if v___x_5918_ == 0 {
                return v___x_5911_;
            } else {
                let mut v___x_5919_: u8 = 0;
                v___x_5919_ = 0;
                return v___x_5919_;
            }
        }
    }
}
pub unsafe fn l_Vector_all___boxed(
    mut v_00_u03b1_5920_: *mut leanh::LeanObject,
    mut v_n_5921_: *mut leanh::LeanObject,
    mut v_xs_5922_: *mut leanh::LeanObject,
    mut v_p_5923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5924_: u8 = 0;
    let mut v_r_5925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5924_ = l_Vector_all(v_00_u03b1_5920_, v_n_5921_, v_xs_5922_, v_p_5923_);
    leanh::lean_dec(v_n_5921_);
    v_r_5925_ = leanh::lean_box((v_res_5924_) as usize);
    return v_r_5925_;
}
pub unsafe fn l_Vector_countP___redArg___lam__0(
    mut v_p_5926_: *mut leanh::LeanObject,
    mut v_x1_5927_: *mut leanh::LeanObject,
    mut v_x2_5928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: u8 = 0;
    v___x_5929_ = leanh::lean_apply_1(v_p_5926_, v_x1_5927_);
    v___x_5930_ = (leanh::lean_unbox(v___x_5929_) as u8);
    if v___x_5930_ == 0 {
        leanh::lean_inc(v_x2_5928_);
        return v_x2_5928_;
    } else {
        let mut v___x_5931_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5931_ = leanh::lean_unsigned_to_nat(1);
        v___x_5932_ = lean_nat_add(v_x2_5928_, v___x_5931_);
        return v___x_5932_;
    }
}
pub unsafe fn l_Vector_countP___redArg___lam__0___boxed(
    mut v_p_5933_: *mut leanh::LeanObject,
    mut v_x1_5934_: *mut leanh::LeanObject,
    mut v_x2_5935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5936_ = l_Vector_countP___redArg___lam__0(v_p_5933_, v_x1_5934_, v_x2_5935_);
    leanh::lean_dec(v_x2_5935_);
    return v_res_5936_;
}
pub unsafe fn l_Vector_countP___redArg(
    mut v_p_5937_: *mut leanh::LeanObject,
    mut v_xs_5938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: u8 = 0;
    v___x_5939_ = leanh::lean_unsigned_to_nat(0);
    v___x_5940_ = lean_array_get_size(v_xs_5938_);
    v___x_5941_ = l_Vector_foldl___redArg___closed__9;
    v___x_5942_ = lean_nat_dec_lt(v___x_5939_, v___x_5940_);
    if v___x_5942_ == 0 {
        leanh::lean_dec_ref(v_xs_5938_);
        leanh::lean_dec_ref(v_p_5937_);
        return v___x_5939_;
    } else {
        let mut v___f_5943_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5944_: usize = 0;
        let mut v___x_5945_: usize = 0;
        let mut v___x_5946_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_5943_ = leanh::lean_alloc_closure(
            l_Vector_countP___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_5943_, 0, v_p_5937_);
        v___x_5944_ = lean_usize_of_nat(v___x_5940_);
        v___x_5945_ = 0usize;
        v___x_5946_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_5941_,
            v___f_5943_,
            v_xs_5938_,
            v___x_5944_,
            v___x_5945_,
            v___x_5939_,
        );
        return v___x_5946_;
    }
}
pub unsafe fn l_Vector_countP(
    mut v_00_u03b1_5947_: *mut leanh::LeanObject,
    mut v_n_5948_: *mut leanh::LeanObject,
    mut v_p_5949_: *mut leanh::LeanObject,
    mut v_xs_5950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: u8 = 0;
    v___x_5951_ = leanh::lean_unsigned_to_nat(0);
    v___x_5952_ = lean_array_get_size(v_xs_5950_);
    v___x_5953_ = l_Vector_foldl___redArg___closed__9;
    v___x_5954_ = lean_nat_dec_lt(v___x_5951_, v___x_5952_);
    if v___x_5954_ == 0 {
        leanh::lean_dec_ref(v_xs_5950_);
        leanh::lean_dec_ref(v_p_5949_);
        return v___x_5951_;
    } else {
        let mut v___f_5955_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5956_: usize = 0;
        let mut v___x_5957_: usize = 0;
        let mut v___x_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_5955_ = leanh::lean_alloc_closure(
            l_Vector_countP___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_5955_, 0, v_p_5949_);
        v___x_5956_ = lean_usize_of_nat(v___x_5952_);
        v___x_5957_ = 0usize;
        v___x_5958_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_5953_,
            v___f_5955_,
            v_xs_5950_,
            v___x_5956_,
            v___x_5957_,
            v___x_5951_,
        );
        return v___x_5958_;
    }
}
pub unsafe fn l_Vector_countP___boxed(
    mut v_00_u03b1_5959_: *mut leanh::LeanObject,
    mut v_n_5960_: *mut leanh::LeanObject,
    mut v_p_5961_: *mut leanh::LeanObject,
    mut v_xs_5962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5963_ = l_Vector_countP(v_00_u03b1_5959_, v_n_5960_, v_p_5961_, v_xs_5962_);
    leanh::lean_dec(v_n_5960_);
    return v_res_5963_;
}
pub unsafe fn l_Vector_count___redArg___lam__0(
    mut v_inst_5964_: *mut leanh::LeanObject,
    mut v_a_5965_: *mut leanh::LeanObject,
    mut v_x1_5966_: *mut leanh::LeanObject,
    mut v_x2_5967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: u8 = 0;
    v___x_5968_ = leanh::lean_apply_2(v_inst_5964_, v_x1_5966_, v_a_5965_);
    v___x_5969_ = (leanh::lean_unbox(v___x_5968_) as u8);
    if v___x_5969_ == 0 {
        leanh::lean_inc(v_x2_5967_);
        return v_x2_5967_;
    } else {
        let mut v___x_5970_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5970_ = leanh::lean_unsigned_to_nat(1);
        v___x_5971_ = lean_nat_add(v_x2_5967_, v___x_5970_);
        return v___x_5971_;
    }
}
pub unsafe fn l_Vector_count___redArg___lam__0___boxed(
    mut v_inst_5972_: *mut leanh::LeanObject,
    mut v_a_5973_: *mut leanh::LeanObject,
    mut v_x1_5974_: *mut leanh::LeanObject,
    mut v_x2_5975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5976_ = l_Vector_count___redArg___lam__0(v_inst_5972_, v_a_5973_, v_x1_5974_, v_x2_5975_);
    leanh::lean_dec(v_x2_5975_);
    return v_res_5976_;
}
pub unsafe fn l_Vector_count___redArg(
    mut v_inst_5977_: *mut leanh::LeanObject,
    mut v_a_5978_: *mut leanh::LeanObject,
    mut v_xs_5979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: u8 = 0;
    v___x_5980_ = leanh::lean_unsigned_to_nat(0);
    v___x_5981_ = lean_array_get_size(v_xs_5979_);
    v___x_5982_ = l_Vector_foldl___redArg___closed__9;
    v___x_5983_ = lean_nat_dec_lt(v___x_5980_, v___x_5981_);
    if v___x_5983_ == 0 {
        leanh::lean_dec_ref(v_xs_5979_);
        leanh::lean_dec(v_a_5978_);
        leanh::lean_dec_ref(v_inst_5977_);
        return v___x_5980_;
    } else {
        let mut v___f_5984_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5985_: usize = 0;
        let mut v___x_5986_: usize = 0;
        let mut v___x_5987_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_5984_ = leanh::lean_alloc_closure(
            l_Vector_count___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_5984_, 0, v_inst_5977_);
        leanh::lean_closure_set(v___f_5984_, 1, v_a_5978_);
        v___x_5985_ = lean_usize_of_nat(v___x_5981_);
        v___x_5986_ = 0usize;
        v___x_5987_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_5982_,
            v___f_5984_,
            v_xs_5979_,
            v___x_5985_,
            v___x_5986_,
            v___x_5980_,
        );
        return v___x_5987_;
    }
}
pub unsafe fn l_Vector_count(
    mut v_00_u03b1_5988_: *mut leanh::LeanObject,
    mut v_n_5989_: *mut leanh::LeanObject,
    mut v_inst_5990_: *mut leanh::LeanObject,
    mut v_a_5991_: *mut leanh::LeanObject,
    mut v_xs_5992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: u8 = 0;
    v___x_5993_ = leanh::lean_unsigned_to_nat(0);
    v___x_5994_ = lean_array_get_size(v_xs_5992_);
    v___x_5995_ = l_Vector_foldl___redArg___closed__9;
    v___x_5996_ = lean_nat_dec_lt(v___x_5993_, v___x_5994_);
    if v___x_5996_ == 0 {
        leanh::lean_dec_ref(v_xs_5992_);
        leanh::lean_dec(v_a_5991_);
        leanh::lean_dec_ref(v_inst_5990_);
        return v___x_5993_;
    } else {
        let mut v___f_5997_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5998_: usize = 0;
        let mut v___x_5999_: usize = 0;
        let mut v___x_6000_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_5997_ = leanh::lean_alloc_closure(
            l_Vector_count___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            2,
        );
        leanh::lean_closure_set(v___f_5997_, 0, v_inst_5990_);
        leanh::lean_closure_set(v___f_5997_, 1, v_a_5991_);
        v___x_5998_ = lean_usize_of_nat(v___x_5994_);
        v___x_5999_ = 0usize;
        v___x_6000_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_5995_,
            v___f_5997_,
            v_xs_5992_,
            v___x_5998_,
            v___x_5999_,
            v___x_5993_,
        );
        return v___x_6000_;
    }
}
pub unsafe fn l_Vector_count___boxed(
    mut v_00_u03b1_6001_: *mut leanh::LeanObject,
    mut v_n_6002_: *mut leanh::LeanObject,
    mut v_inst_6003_: *mut leanh::LeanObject,
    mut v_a_6004_: *mut leanh::LeanObject,
    mut v_xs_6005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6006_ = l_Vector_count(
        v_00_u03b1_6001_,
        v_n_6002_,
        v_inst_6003_,
        v_a_6004_,
        v_xs_6005_,
    );
    leanh::lean_dec(v_n_6002_);
    return v_res_6006_;
}
pub unsafe fn l_Vector_replace___redArg(
    mut v_inst_6007_: *mut leanh::LeanObject,
    mut v_xs_6008_: *mut leanh::LeanObject,
    mut v_a_6009_: *mut leanh::LeanObject,
    mut v_b_6010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6011_ = l_Array_replace___redArg(v_inst_6007_, v_xs_6008_, v_a_6009_, v_b_6010_);
    return v___x_6011_;
}
pub unsafe fn l_Vector_replace(
    mut v_00_u03b1_6012_: *mut leanh::LeanObject,
    mut v_n_6013_: *mut leanh::LeanObject,
    mut v_inst_6014_: *mut leanh::LeanObject,
    mut v_xs_6015_: *mut leanh::LeanObject,
    mut v_a_6016_: *mut leanh::LeanObject,
    mut v_b_6017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6018_ = l_Array_replace___redArg(v_inst_6014_, v_xs_6015_, v_a_6016_, v_b_6017_);
    return v___x_6018_;
}
pub unsafe fn l_Vector_replace___boxed(
    mut v_00_u03b1_6019_: *mut leanh::LeanObject,
    mut v_n_6020_: *mut leanh::LeanObject,
    mut v_inst_6021_: *mut leanh::LeanObject,
    mut v_xs_6022_: *mut leanh::LeanObject,
    mut v_a_6023_: *mut leanh::LeanObject,
    mut v_b_6024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6025_ = l_Vector_replace(
        v_00_u03b1_6019_,
        v_n_6020_,
        v_inst_6021_,
        v_xs_6022_,
        v_a_6023_,
        v_b_6024_,
    );
    leanh::lean_dec(v_n_6020_);
    return v_res_6025_;
}
pub unsafe fn l_Vector_sum___redArg___lam__0(
    mut v_inst_6026_: *mut leanh::LeanObject,
    mut v_x1_6027_: *mut leanh::LeanObject,
    mut v_x2_6028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6029_ = leanh::lean_apply_2(v_inst_6026_, v_x1_6027_, v_x2_6028_);
    return v___x_6029_;
}
pub unsafe fn l_Vector_sum___redArg(
    mut v_inst_6030_: *mut leanh::LeanObject,
    mut v_inst_6031_: *mut leanh::LeanObject,
    mut v_xs_6032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: u8 = 0;
    v___x_6033_ = lean_array_get_size(v_xs_6032_);
    v___x_6034_ = leanh::lean_unsigned_to_nat(0);
    v___x_6035_ = l_Vector_foldl___redArg___closed__9;
    v___x_6036_ = lean_nat_dec_lt(v___x_6034_, v___x_6033_);
    if v___x_6036_ == 0 {
        leanh::lean_dec_ref(v_xs_6032_);
        leanh::lean_dec(v_inst_6030_);
        return v_inst_6031_;
    } else {
        let mut v___f_6037_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6038_: usize = 0;
        let mut v___x_6039_: usize = 0;
        let mut v___x_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_6037_ = leanh::lean_alloc_closure(
            l_Vector_sum___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_6037_, 0, v_inst_6030_);
        v___x_6038_ = lean_usize_of_nat(v___x_6033_);
        v___x_6039_ = 0usize;
        v___x_6040_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_6035_,
            v___f_6037_,
            v_xs_6032_,
            v___x_6038_,
            v___x_6039_,
            v_inst_6031_,
        );
        return v___x_6040_;
    }
}
pub unsafe fn l_Vector_sum(
    mut v_00_u03b1_6041_: *mut leanh::LeanObject,
    mut v_n_6042_: *mut leanh::LeanObject,
    mut v_inst_6043_: *mut leanh::LeanObject,
    mut v_inst_6044_: *mut leanh::LeanObject,
    mut v_xs_6045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: u8 = 0;
    v___x_6046_ = lean_array_get_size(v_xs_6045_);
    v___x_6047_ = leanh::lean_unsigned_to_nat(0);
    v___x_6048_ = l_Vector_foldl___redArg___closed__9;
    v___x_6049_ = lean_nat_dec_lt(v___x_6047_, v___x_6046_);
    if v___x_6049_ == 0 {
        leanh::lean_dec_ref(v_xs_6045_);
        leanh::lean_dec(v_inst_6043_);
        return v_inst_6044_;
    } else {
        let mut v___f_6050_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6051_: usize = 0;
        let mut v___x_6052_: usize = 0;
        let mut v___x_6053_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_6050_ = leanh::lean_alloc_closure(
            l_Vector_sum___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_6050_, 0, v_inst_6043_);
        v___x_6051_ = lean_usize_of_nat(v___x_6046_);
        v___x_6052_ = 0usize;
        v___x_6053_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_6048_,
            v___f_6050_,
            v_xs_6045_,
            v___x_6051_,
            v___x_6052_,
            v_inst_6044_,
        );
        return v___x_6053_;
    }
}
pub unsafe fn l_Vector_sum___boxed(
    mut v_00_u03b1_6054_: *mut leanh::LeanObject,
    mut v_n_6055_: *mut leanh::LeanObject,
    mut v_inst_6056_: *mut leanh::LeanObject,
    mut v_inst_6057_: *mut leanh::LeanObject,
    mut v_xs_6058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6059_ = l_Vector_sum(
        v_00_u03b1_6054_,
        v_n_6055_,
        v_inst_6056_,
        v_inst_6057_,
        v_xs_6058_,
    );
    leanh::lean_dec(v_n_6055_);
    return v_res_6059_;
}
pub unsafe fn l_Vector_prod___redArg(
    mut v_inst_6060_: *mut leanh::LeanObject,
    mut v_inst_6061_: *mut leanh::LeanObject,
    mut v_xs_6062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: u8 = 0;
    v___x_6063_ = lean_array_get_size(v_xs_6062_);
    v___x_6064_ = leanh::lean_unsigned_to_nat(0);
    v___x_6065_ = l_Vector_foldl___redArg___closed__9;
    v___x_6066_ = lean_nat_dec_lt(v___x_6064_, v___x_6063_);
    if v___x_6066_ == 0 {
        leanh::lean_dec_ref(v_xs_6062_);
        leanh::lean_dec(v_inst_6060_);
        return v_inst_6061_;
    } else {
        let mut v___f_6067_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6068_: usize = 0;
        let mut v___x_6069_: usize = 0;
        let mut v___x_6070_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_6067_ = leanh::lean_alloc_closure(
            l_Vector_sum___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_6067_, 0, v_inst_6060_);
        v___x_6068_ = lean_usize_of_nat(v___x_6063_);
        v___x_6069_ = 0usize;
        v___x_6070_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_6065_,
            v___f_6067_,
            v_xs_6062_,
            v___x_6068_,
            v___x_6069_,
            v_inst_6061_,
        );
        return v___x_6070_;
    }
}
pub unsafe fn l_Vector_prod(
    mut v_00_u03b1_6071_: *mut leanh::LeanObject,
    mut v_n_6072_: *mut leanh::LeanObject,
    mut v_inst_6073_: *mut leanh::LeanObject,
    mut v_inst_6074_: *mut leanh::LeanObject,
    mut v_xs_6075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6079_: u8 = 0;
    v___x_6076_ = lean_array_get_size(v_xs_6075_);
    v___x_6077_ = leanh::lean_unsigned_to_nat(0);
    v___x_6078_ = l_Vector_foldl___redArg___closed__9;
    v___x_6079_ = lean_nat_dec_lt(v___x_6077_, v___x_6076_);
    if v___x_6079_ == 0 {
        leanh::lean_dec_ref(v_xs_6075_);
        leanh::lean_dec(v_inst_6073_);
        return v_inst_6074_;
    } else {
        let mut v___f_6080_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6081_: usize = 0;
        let mut v___x_6082_: usize = 0;
        let mut v___x_6083_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_6080_ = leanh::lean_alloc_closure(
            l_Vector_sum___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_6080_, 0, v_inst_6073_);
        v___x_6081_ = lean_usize_of_nat(v___x_6076_);
        v___x_6082_ = 0usize;
        v___x_6083_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_6078_,
            v___f_6080_,
            v_xs_6075_,
            v___x_6081_,
            v___x_6082_,
            v_inst_6074_,
        );
        return v___x_6083_;
    }
}
pub unsafe fn l_Vector_prod___boxed(
    mut v_00_u03b1_6084_: *mut leanh::LeanObject,
    mut v_n_6085_: *mut leanh::LeanObject,
    mut v_inst_6086_: *mut leanh::LeanObject,
    mut v_inst_6087_: *mut leanh::LeanObject,
    mut v_xs_6088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6089_ = l_Vector_prod(
        v_00_u03b1_6084_,
        v_n_6085_,
        v_inst_6086_,
        v_inst_6087_,
        v_xs_6088_,
    );
    leanh::lean_dec(v_n_6085_);
    return v_res_6089_;
}
pub unsafe fn l_Vector_leftpad___redArg(
    mut v_m_6090_: *mut leanh::LeanObject,
    mut v_n_6091_: *mut leanh::LeanObject,
    mut v_a_6092_: *mut leanh::LeanObject,
    mut v_xs_6093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6094_ = lean_nat_sub(v_n_6091_, v_m_6090_);
    v___x_6095_ = lean_mk_array(v___x_6094_, v_a_6092_);
    v___x_6096_ = l_Array_append___redArg(v___x_6095_, v_xs_6093_);
    return v___x_6096_;
}
pub unsafe fn l_Vector_leftpad___redArg___boxed(
    mut v_m_6097_: *mut leanh::LeanObject,
    mut v_n_6098_: *mut leanh::LeanObject,
    mut v_a_6099_: *mut leanh::LeanObject,
    mut v_xs_6100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6101_ = l_Vector_leftpad___redArg(v_m_6097_, v_n_6098_, v_a_6099_, v_xs_6100_);
    leanh::lean_dec_ref(v_xs_6100_);
    leanh::lean_dec(v_n_6098_);
    leanh::lean_dec(v_m_6097_);
    return v_res_6101_;
}
pub unsafe fn l_Vector_leftpad(
    mut v_00_u03b1_6102_: *mut leanh::LeanObject,
    mut v_m_6103_: *mut leanh::LeanObject,
    mut v_n_6104_: *mut leanh::LeanObject,
    mut v_a_6105_: *mut leanh::LeanObject,
    mut v_xs_6106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6107_ = lean_nat_sub(v_n_6104_, v_m_6103_);
    v___x_6108_ = lean_mk_array(v___x_6107_, v_a_6105_);
    v___x_6109_ = l_Array_append___redArg(v___x_6108_, v_xs_6106_);
    return v___x_6109_;
}
pub unsafe fn l_Vector_leftpad___boxed(
    mut v_00_u03b1_6110_: *mut leanh::LeanObject,
    mut v_m_6111_: *mut leanh::LeanObject,
    mut v_n_6112_: *mut leanh::LeanObject,
    mut v_a_6113_: *mut leanh::LeanObject,
    mut v_xs_6114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6115_ = l_Vector_leftpad(
        v_00_u03b1_6110_,
        v_m_6111_,
        v_n_6112_,
        v_a_6113_,
        v_xs_6114_,
    );
    leanh::lean_dec_ref(v_xs_6114_);
    leanh::lean_dec(v_n_6112_);
    leanh::lean_dec(v_m_6111_);
    return v_res_6115_;
}
pub unsafe fn l_Vector_rightpad___redArg(
    mut v_m_6116_: *mut leanh::LeanObject,
    mut v_n_6117_: *mut leanh::LeanObject,
    mut v_a_6118_: *mut leanh::LeanObject,
    mut v_xs_6119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6120_ = lean_nat_sub(v_n_6117_, v_m_6116_);
    v___x_6121_ = lean_mk_array(v___x_6120_, v_a_6118_);
    v___x_6122_ = l_Array_append___redArg(v_xs_6119_, v___x_6121_);
    leanh::lean_dec_ref(v___x_6121_);
    return v___x_6122_;
}
pub unsafe fn l_Vector_rightpad___redArg___boxed(
    mut v_m_6123_: *mut leanh::LeanObject,
    mut v_n_6124_: *mut leanh::LeanObject,
    mut v_a_6125_: *mut leanh::LeanObject,
    mut v_xs_6126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6127_ = l_Vector_rightpad___redArg(v_m_6123_, v_n_6124_, v_a_6125_, v_xs_6126_);
    leanh::lean_dec(v_n_6124_);
    leanh::lean_dec(v_m_6123_);
    return v_res_6127_;
}
pub unsafe fn l_Vector_rightpad(
    mut v_00_u03b1_6128_: *mut leanh::LeanObject,
    mut v_m_6129_: *mut leanh::LeanObject,
    mut v_n_6130_: *mut leanh::LeanObject,
    mut v_a_6131_: *mut leanh::LeanObject,
    mut v_xs_6132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6133_ = lean_nat_sub(v_n_6130_, v_m_6129_);
    v___x_6134_ = lean_mk_array(v___x_6133_, v_a_6131_);
    v___x_6135_ = l_Array_append___redArg(v_xs_6132_, v___x_6134_);
    leanh::lean_dec_ref(v___x_6134_);
    return v___x_6135_;
}
pub unsafe fn l_Vector_rightpad___boxed(
    mut v_00_u03b1_6136_: *mut leanh::LeanObject,
    mut v_m_6137_: *mut leanh::LeanObject,
    mut v_n_6138_: *mut leanh::LeanObject,
    mut v_a_6139_: *mut leanh::LeanObject,
    mut v_xs_6140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6141_ = l_Vector_rightpad(
        v_00_u03b1_6136_,
        v_m_6137_,
        v_n_6138_,
        v_a_6139_,
        v_xs_6140_,
    );
    leanh::lean_dec(v_n_6138_);
    leanh::lean_dec(v_m_6137_);
    return v_res_6141_;
}
pub unsafe fn l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(
    mut v_f_6142_: *mut leanh::LeanObject,
    mut v_a_6143_: *mut leanh::LeanObject,
    mut v_h_6144_: *mut leanh::LeanObject,
    mut v_b_6145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6146_ =
        leanh::lean_apply_3(v_f_6142_, v_a_6143_, leanh::lean_box(0), v_b_6145_);
    return v___x_6146_;
}
pub unsafe fn l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1(
    mut v_inst_6147_: *mut leanh::LeanObject,
    mut v_00_u03b2_6148_: *mut leanh::LeanObject,
    mut v_xs_6149_: *mut leanh::LeanObject,
    mut v_b_6150_: *mut leanh::LeanObject,
    mut v_f_6151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6153_: usize = 0;
    let mut v___x_6154_: usize = 0;
    let mut v___x_6155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6152_ = leanh::lean_alloc_closure(
        l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_6152_, 0, v_f_6151_);
    v_sz_6153_ = lean_array_size(v_xs_6149_);
    v___x_6154_ = 0usize;
    v___x_6155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_6147_,
        v_xs_6149_,
        v___f_6152_,
        v_sz_6153_,
        v___x_6154_,
        v_b_6150_,
    );
    return v___x_6155_;
}
pub unsafe fn l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg(
    mut v_inst_6156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6157_ = leanh::lean_alloc_closure(
        l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_6157_, 0, v_inst_6156_);
    return v___f_6157_;
}
pub unsafe fn l_Vector_instForIn_x27InferInstanceMembershipOfMonad(
    mut v_m_6158_: *mut leanh::LeanObject,
    mut v_00_u03b1_6159_: *mut leanh::LeanObject,
    mut v_n_6160_: *mut leanh::LeanObject,
    mut v_inst_6161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6162_ = leanh::lean_alloc_closure(
        l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_6162_, 0, v_inst_6161_);
    return v___f_6162_;
}
pub unsafe fn l_Vector_instForIn_x27InferInstanceMembershipOfMonad___boxed(
    mut v_m_6163_: *mut leanh::LeanObject,
    mut v_00_u03b1_6164_: *mut leanh::LeanObject,
    mut v_n_6165_: *mut leanh::LeanObject,
    mut v_inst_6166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6167_ = l_Vector_instForIn_x27InferInstanceMembershipOfMonad(
        v_m_6163_,
        v_00_u03b1_6164_,
        v_n_6165_,
        v_inst_6166_,
    );
    leanh::lean_dec(v_n_6165_);
    return v_res_6167_;
}
pub unsafe fn l_Vector_instForMOfMonad___redArg(
    mut v_n_6168_: *mut leanh::LeanObject,
    mut v_inst_6169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6170_ =
        leanh::lean_alloc_closure(l_Vector_forM___boxed as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_6170_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_6170_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_6170_, 2, v_n_6168_);
    leanh::lean_closure_set(v___x_6170_, 3, v_inst_6169_);
    return v___x_6170_;
}
pub unsafe fn l_Vector_instForMOfMonad(
    mut v_m_6171_: *mut leanh::LeanObject,
    mut v_00_u03b1_6172_: *mut leanh::LeanObject,
    mut v_n_6173_: *mut leanh::LeanObject,
    mut v_inst_6174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6175_ =
        leanh::lean_alloc_closure(l_Vector_forM___boxed as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_6175_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_6175_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_6175_, 2, v_n_6173_);
    leanh::lean_closure_set(v___x_6175_, 3, v_inst_6174_);
    return v___x_6175_;
}
pub unsafe fn l_Vector_instLT(
    mut v_00_u03b1_6176_: *mut leanh::LeanObject,
    mut v_n_6177_: *mut leanh::LeanObject,
    mut v_inst_6178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6179_ = leanh::lean_box(0);
    return v___x_6179_;
}
pub unsafe fn l_Vector_instLT___boxed(
    mut v_00_u03b1_6180_: *mut leanh::LeanObject,
    mut v_n_6181_: *mut leanh::LeanObject,
    mut v_inst_6182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6183_ = l_Vector_instLT(v_00_u03b1_6180_, v_n_6181_, v_inst_6182_);
    leanh::lean_dec(v_n_6181_);
    return v_res_6183_;
}
pub unsafe fn l_Vector_instLE(
    mut v_00_u03b1_6184_: *mut leanh::LeanObject,
    mut v_n_6185_: *mut leanh::LeanObject,
    mut v_inst_6186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6187_ = leanh::lean_box(0);
    return v___x_6187_;
}
pub unsafe fn l_Vector_instLE___boxed(
    mut v_00_u03b1_6188_: *mut leanh::LeanObject,
    mut v_n_6189_: *mut leanh::LeanObject,
    mut v_inst_6190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6191_ = l_Vector_instLE(v_00_u03b1_6188_, v_n_6189_, v_inst_6190_);
    leanh::lean_dec(v_n_6189_);
    return v_res_6191_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_6198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6198_ = l_Vector_lex___auto__1___closed__0;
    v___x_6199_ = l_Lean_mkAtom(v___x_6198_);
    return v___x_6199_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_6200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6200_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__2),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__2_once),
        _init_l_Vector_lex___auto__1___closed__2,
    );
    v___x_6201_ = l_Vector_set___auto__1___closed__3;
    v___x_6202_ = lean_array_push(v___x_6201_, v___x_6200_);
    return v___x_6202_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_6215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6215_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17;
    v___x_6216_ = l_Lean_mkAtom(v___x_6215_);
    return v___x_6216_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_6217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6217_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__8),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__8_once),
        _init_l_Vector_lex___auto__1___closed__8,
    );
    v___x_6218_ = l_Vector_set___auto__1___closed__3;
    v___x_6219_ = lean_array_push(v___x_6218_, v___x_6217_);
    return v___x_6219_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_6224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6224_ = l_Vector_lex___auto__1___closed__12;
    v___x_6225_ = lean_string_utf8_byte_size(v___x_6224_);
    return v___x_6225_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__14() -> *mut leanh::LeanObject {
    let mut v___x_6226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6226_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__13_once),
        _init_l_Vector_lex___auto__1___closed__13,
    );
    v___x_6227_ = leanh::lean_unsigned_to_nat(0);
    v___x_6228_ = l_Vector_lex___auto__1___closed__12;
    v___x_6229_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6229_, 0, v___x_6228_);
    leanh::lean_ctor_set(v___x_6229_, 1, v___x_6227_);
    leanh::lean_ctor_set(v___x_6229_, 2, v___x_6226_);
    return v___x_6229_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_6230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6230_ = leanh::lean_box(0);
    v___x_6231_ = leanh::lean_box(0);
    v___x_6232_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__14),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__14_once),
        _init_l_Vector_lex___auto__1___closed__14,
    );
    v___x_6233_ = leanh::lean_box(2);
    v___x_6234_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_6234_, 0, v___x_6233_);
    leanh::lean_ctor_set(v___x_6234_, 1, v___x_6232_);
    leanh::lean_ctor_set(v___x_6234_, 2, v___x_6231_);
    leanh::lean_ctor_set(v___x_6234_, 3, v___x_6230_);
    return v___x_6234_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__16() -> *mut leanh::LeanObject {
    let mut v___x_6235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6235_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__15_once),
        _init_l_Vector_lex___auto__1___closed__15,
    );
    v___x_6236_ = l_Vector_set___auto__1___closed__3;
    v___x_6237_ = lean_array_push(v___x_6236_, v___x_6235_);
    return v___x_6237_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__17() -> *mut leanh::LeanObject {
    let mut v___x_6238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6238_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__16_once),
        _init_l_Vector_lex___auto__1___closed__16,
    );
    v___x_6239_ = l_Vector_lex___auto__1___closed__11;
    v___x_6240_ = leanh::lean_box(2);
    v___x_6241_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6241_, 0, v___x_6240_);
    leanh::lean_ctor_set(v___x_6241_, 1, v___x_6239_);
    leanh::lean_ctor_set(v___x_6241_, 2, v___x_6238_);
    return v___x_6241_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__18() -> *mut leanh::LeanObject {
    let mut v___x_6242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6242_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__17_once),
        _init_l_Vector_lex___auto__1___closed__17,
    );
    v___x_6243_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__9),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__9_once),
        _init_l_Vector_lex___auto__1___closed__9,
    );
    v___x_6244_ = lean_array_push(v___x_6243_, v___x_6242_);
    return v___x_6244_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__19() -> *mut leanh::LeanObject {
    let mut v___x_6245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6245_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__18_once),
        _init_l_Vector_lex___auto__1___closed__18,
    );
    v___x_6246_ = l_Vector_lex___auto__1___closed__7;
    v___x_6247_ = leanh::lean_box(2);
    v___x_6248_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6248_, 0, v___x_6247_);
    leanh::lean_ctor_set(v___x_6248_, 1, v___x_6246_);
    leanh::lean_ctor_set(v___x_6248_, 2, v___x_6245_);
    return v___x_6248_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__20() -> *mut leanh::LeanObject {
    let mut v___x_6249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6249_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__19_once),
        _init_l_Vector_lex___auto__1___closed__19,
    );
    v___x_6250_ = l_Vector_set___auto__1___closed__3;
    v___x_6251_ = lean_array_push(v___x_6250_, v___x_6249_);
    return v___x_6251_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__26() -> *mut leanh::LeanObject {
    let mut v___x_6262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6262_ = l_Vector_lex___auto__1___closed__25;
    v___x_6263_ = l_Lean_mkAtom(v___x_6262_);
    return v___x_6263_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__27() -> *mut leanh::LeanObject {
    let mut v___x_6264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6264_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__26_once),
        _init_l_Vector_lex___auto__1___closed__26,
    );
    v___x_6265_ = l_Vector_set___auto__1___closed__3;
    v___x_6266_ = lean_array_push(v___x_6265_, v___x_6264_);
    return v___x_6266_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__28() -> *mut leanh::LeanObject {
    let mut v___x_6267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6267_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__17_once),
        _init_l_Vector_lex___auto__1___closed__17,
    );
    v___x_6268_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__27_once),
        _init_l_Vector_lex___auto__1___closed__27,
    );
    v___x_6269_ = lean_array_push(v___x_6268_, v___x_6267_);
    return v___x_6269_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__29() -> *mut leanh::LeanObject {
    let mut v___x_6270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6270_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__28_once),
        _init_l_Vector_lex___auto__1___closed__28,
    );
    v___x_6271_ = l_Vector_lex___auto__1___closed__24;
    v___x_6272_ = leanh::lean_box(2);
    v___x_6273_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6273_, 0, v___x_6272_);
    leanh::lean_ctor_set(v___x_6273_, 1, v___x_6271_);
    leanh::lean_ctor_set(v___x_6273_, 2, v___x_6270_);
    return v___x_6273_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__30() -> *mut leanh::LeanObject {
    let mut v___x_6274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6274_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__29_once),
        _init_l_Vector_lex___auto__1___closed__29,
    );
    v___x_6275_ = l_Vector_set___auto__1___closed__3;
    v___x_6276_ = lean_array_push(v___x_6275_, v___x_6274_);
    return v___x_6276_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__32() -> *mut leanh::LeanObject {
    let mut v___x_6278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6278_ = l_Vector_lex___auto__1___closed__31;
    v___x_6279_ = l_Lean_mkAtom(v___x_6278_);
    return v___x_6279_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__33() -> *mut leanh::LeanObject {
    let mut v___x_6280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6280_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__32_once),
        _init_l_Vector_lex___auto__1___closed__32,
    );
    v___x_6281_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__30_once),
        _init_l_Vector_lex___auto__1___closed__30,
    );
    v___x_6282_ = lean_array_push(v___x_6281_, v___x_6280_);
    return v___x_6282_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__34() -> *mut leanh::LeanObject {
    let mut v___x_6283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6283_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__29_once),
        _init_l_Vector_lex___auto__1___closed__29,
    );
    v___x_6284_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__33),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__33_once),
        _init_l_Vector_lex___auto__1___closed__33,
    );
    v___x_6285_ = lean_array_push(v___x_6284_, v___x_6283_);
    return v___x_6285_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__35() -> *mut leanh::LeanObject {
    let mut v___x_6286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6286_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__34),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__34_once),
        _init_l_Vector_lex___auto__1___closed__34,
    );
    v___x_6287_ = l_Vector_lex___auto__1___closed__22;
    v___x_6288_ = leanh::lean_box(2);
    v___x_6289_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6289_, 0, v___x_6288_);
    leanh::lean_ctor_set(v___x_6289_, 1, v___x_6287_);
    leanh::lean_ctor_set(v___x_6289_, 2, v___x_6286_);
    return v___x_6289_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__36() -> *mut leanh::LeanObject {
    let mut v___x_6290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6290_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__35),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__35_once),
        _init_l_Vector_lex___auto__1___closed__35,
    );
    v___x_6291_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__20_once),
        _init_l_Vector_lex___auto__1___closed__20,
    );
    v___x_6292_ = lean_array_push(v___x_6291_, v___x_6290_);
    return v___x_6292_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__37() -> *mut leanh::LeanObject {
    let mut v___x_6293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6293_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22;
    v___x_6294_ = l_Lean_mkAtom(v___x_6293_);
    return v___x_6294_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__38() -> *mut leanh::LeanObject {
    let mut v___x_6295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6295_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__37),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__37_once),
        _init_l_Vector_lex___auto__1___closed__37,
    );
    v___x_6296_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__36),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__36_once),
        _init_l_Vector_lex___auto__1___closed__36,
    );
    v___x_6297_ = lean_array_push(v___x_6296_, v___x_6295_);
    return v___x_6297_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__39() -> *mut leanh::LeanObject {
    let mut v___x_6298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6298_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__38),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__38_once),
        _init_l_Vector_lex___auto__1___closed__38,
    );
    v___x_6299_ = l_Vector_lex___auto__1___closed__5;
    v___x_6300_ = leanh::lean_box(2);
    v___x_6301_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6301_, 0, v___x_6300_);
    leanh::lean_ctor_set(v___x_6301_, 1, v___x_6299_);
    leanh::lean_ctor_set(v___x_6301_, 2, v___x_6298_);
    return v___x_6301_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__40() -> *mut leanh::LeanObject {
    let mut v___x_6302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6302_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__39),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__39_once),
        _init_l_Vector_lex___auto__1___closed__39,
    );
    v___x_6303_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__3),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__3_once),
        _init_l_Vector_lex___auto__1___closed__3,
    );
    v___x_6304_ = lean_array_push(v___x_6303_, v___x_6302_);
    return v___x_6304_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__41() -> *mut leanh::LeanObject {
    let mut v___x_6305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6305_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__40),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__40_once),
        _init_l_Vector_lex___auto__1___closed__40,
    );
    v___x_6306_ = l_Vector_lex___auto__1___closed__1;
    v___x_6307_ = leanh::lean_box(2);
    v___x_6308_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6308_, 0, v___x_6307_);
    leanh::lean_ctor_set(v___x_6308_, 1, v___x_6306_);
    leanh::lean_ctor_set(v___x_6308_, 2, v___x_6305_);
    return v___x_6308_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__42() -> *mut leanh::LeanObject {
    let mut v___x_6309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6309_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__41),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__41_once),
        _init_l_Vector_lex___auto__1___closed__41,
    );
    v___x_6310_ = l_Vector_set___auto__1___closed__3;
    v___x_6311_ = lean_array_push(v___x_6310_, v___x_6309_);
    return v___x_6311_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__43() -> *mut leanh::LeanObject {
    let mut v___x_6312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6312_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__42),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__42_once),
        _init_l_Vector_lex___auto__1___closed__42,
    );
    v___x_6313_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14;
    v___x_6314_ = leanh::lean_box(2);
    v___x_6315_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6315_, 0, v___x_6314_);
    leanh::lean_ctor_set(v___x_6315_, 1, v___x_6313_);
    leanh::lean_ctor_set(v___x_6315_, 2, v___x_6312_);
    return v___x_6315_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__44() -> *mut leanh::LeanObject {
    let mut v___x_6316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6316_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__43),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__43_once),
        _init_l_Vector_lex___auto__1___closed__43,
    );
    v___x_6317_ = l_Vector_set___auto__1___closed__3;
    v___x_6318_ = lean_array_push(v___x_6317_, v___x_6316_);
    return v___x_6318_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__45() -> *mut leanh::LeanObject {
    let mut v___x_6319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6319_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__44),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__44_once),
        _init_l_Vector_lex___auto__1___closed__44,
    );
    v___x_6320_ = l_Vector_set___auto__1___closed__5;
    v___x_6321_ = leanh::lean_box(2);
    v___x_6322_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6322_, 0, v___x_6321_);
    leanh::lean_ctor_set(v___x_6322_, 1, v___x_6320_);
    leanh::lean_ctor_set(v___x_6322_, 2, v___x_6319_);
    return v___x_6322_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__46() -> *mut leanh::LeanObject {
    let mut v___x_6323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6323_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__45),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__45_once),
        _init_l_Vector_lex___auto__1___closed__45,
    );
    v___x_6324_ = l_Vector_set___auto__1___closed__3;
    v___x_6325_ = lean_array_push(v___x_6324_, v___x_6323_);
    return v___x_6325_;
}
pub unsafe fn _init_l_Vector_lex___auto__1___closed__47() -> *mut leanh::LeanObject {
    let mut v___x_6326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6326_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__46),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__46_once),
        _init_l_Vector_lex___auto__1___closed__46,
    );
    v___x_6327_ = l_Vector_set___auto__1___closed__2;
    v___x_6328_ = leanh::lean_box(2);
    v___x_6329_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6329_, 0, v___x_6328_);
    leanh::lean_ctor_set(v___x_6329_, 1, v___x_6327_);
    leanh::lean_ctor_set(v___x_6329_, 2, v___x_6326_);
    return v___x_6329_;
}
pub unsafe fn _init_l_Vector_lex___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_6330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6330_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__47),
        core::ptr::addr_of_mut!(l_Vector_lex___auto__1___closed__47_once),
        _init_l_Vector_lex___auto__1___closed__47,
    );
    return v___x_6330_;
}
pub unsafe fn l_Vector_lex___redArg___lam__0(
    mut v_n_6331_: *mut leanh::LeanObject,
    mut v_xs_6332_: *mut leanh::LeanObject,
    mut v_ys_6333_: *mut leanh::LeanObject,
    mut v_lt_6334_: *mut leanh::LeanObject,
    mut v_inst_6335_: *mut leanh::LeanObject,
    mut v___x_6336_: *mut leanh::LeanObject,
    mut v___x_6337_: *mut leanh::LeanObject,
    mut v_next_6338_: *mut leanh::LeanObject,
    mut v_acc_6339_: *mut leanh::LeanObject,
    mut v_h_6340_: *mut leanh::LeanObject,
    mut v_G_6341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6342_: u8 = 0;
    v___x_6342_ = lean_nat_dec_lt(v_next_6338_, v_n_6331_);
    if v___x_6342_ == 0 {
        leanh::lean_dec_ref(v_G_6341_);
        leanh::lean_dec_ref(v___x_6337_);
        leanh::lean_dec_ref(v_inst_6335_);
        leanh::lean_dec_ref(v_lt_6334_);
        leanh::lean_inc_ref(v_acc_6339_);
        return v_acc_6339_;
    } else {
        let mut v___x_6343_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6344_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6345_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6346_: u8 = 0;
        v___x_6343_ = lean_array_fget_borrowed(v_xs_6332_, v_next_6338_);
        v___x_6344_ = lean_array_fget_borrowed(v_ys_6333_, v_next_6338_);
        leanh::lean_inc(v___x_6344_);
        leanh::lean_inc(v___x_6343_);
        v___x_6345_ = leanh::lean_apply_2(v_lt_6334_, v___x_6343_, v___x_6344_);
        v___x_6346_ = (leanh::lean_unbox(v___x_6345_) as u8);
        if v___x_6346_ == 0 {
            let mut v___x_6347_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6348_: u8 = 0;
            leanh::lean_inc(v___x_6344_);
            leanh::lean_inc(v___x_6343_);
            v___x_6347_ = leanh::lean_apply_2(v_inst_6335_, v___x_6343_, v___x_6344_);
            v___x_6348_ = (leanh::lean_unbox(v___x_6347_) as u8);
            if v___x_6348_ == 0 {
                let mut v___x_6349_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6350_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_G_6341_);
                leanh::lean_dec_ref(v___x_6337_);
                v___x_6349_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6349_, 0, v___x_6345_);
                v___x_6350_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6350_, 0, v___x_6349_);
                leanh::lean_ctor_set(v___x_6350_, 1, v___x_6336_);
                return v___x_6350_;
            } else {
                let mut v___x_6351_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6352_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6353_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_6351_ = leanh::lean_unsigned_to_nat(1);
                v___x_6352_ = lean_nat_add(v_next_6338_, v___x_6351_);
                v___x_6353_ = leanh::lean_apply_4(
                    v_G_6341_,
                    v___x_6352_,
                    v___x_6337_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_6353_;
            }
        } else {
            let mut v___x_6354_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6355_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_G_6341_);
            leanh::lean_dec_ref(v___x_6337_);
            leanh::lean_dec_ref(v_inst_6335_);
            v___x_6354_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_6354_, 0, v___x_6345_);
            v___x_6355_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_6355_, 0, v___x_6354_);
            leanh::lean_ctor_set(v___x_6355_, 1, v___x_6336_);
            return v___x_6355_;
        }
    }
}
pub unsafe fn l_Vector_lex___redArg___lam__0___boxed(
    mut v_n_6356_: *mut leanh::LeanObject,
    mut v_xs_6357_: *mut leanh::LeanObject,
    mut v_ys_6358_: *mut leanh::LeanObject,
    mut v_lt_6359_: *mut leanh::LeanObject,
    mut v_inst_6360_: *mut leanh::LeanObject,
    mut v___x_6361_: *mut leanh::LeanObject,
    mut v___x_6362_: *mut leanh::LeanObject,
    mut v_next_6363_: *mut leanh::LeanObject,
    mut v_acc_6364_: *mut leanh::LeanObject,
    mut v_h_6365_: *mut leanh::LeanObject,
    mut v_G_6366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6367_ = l_Vector_lex___redArg___lam__0(
        v_n_6356_,
        v_xs_6357_,
        v_ys_6358_,
        v_lt_6359_,
        v_inst_6360_,
        v___x_6361_,
        v___x_6362_,
        v_next_6363_,
        v_acc_6364_,
        v_h_6365_,
        v_G_6366_,
    );
    leanh::lean_dec_ref(v_acc_6364_);
    leanh::lean_dec(v_next_6363_);
    leanh::lean_dec_ref(v_ys_6358_);
    leanh::lean_dec_ref(v_xs_6357_);
    leanh::lean_dec(v_n_6356_);
    return v_res_6367_;
}
pub unsafe fn l_Vector_lex___redArg(
    mut v_n_6371_: *mut leanh::LeanObject,
    mut v_inst_6372_: *mut leanh::LeanObject,
    mut v_xs_6373_: *mut leanh::LeanObject,
    mut v_ys_6374_: *mut leanh::LeanObject,
    mut v_lt_6375_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6376_ = leanh::lean_unsigned_to_nat(0);
    v___x_6377_ = leanh::lean_box(0);
    v___x_6378_ = l_Vector_lex___redArg___closed__0;
    v___f_6379_ = leanh::lean_alloc_closure(
        l_Vector_lex___redArg___lam__0___boxed as *mut core::ffi::c_void,
        11,
        7,
    );
    leanh::lean_closure_set(v___f_6379_, 0, v_n_6371_);
    leanh::lean_closure_set(v___f_6379_, 1, v_xs_6373_);
    leanh::lean_closure_set(v___f_6379_, 2, v_ys_6374_);
    leanh::lean_closure_set(v___f_6379_, 3, v_lt_6375_);
    leanh::lean_closure_set(v___f_6379_, 4, v_inst_6372_);
    leanh::lean_closure_set(v___f_6379_, 5, v___x_6377_);
    leanh::lean_closure_set(v___f_6379_, 6, v___x_6378_);
    v___x_6380_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_6379_,
        v___x_6376_,
        v___x_6378_,
        leanh::lean_box(0),
    );
    v_fst_6381_ = leanh::lean_ctor_get(v___x_6380_, 0);
    leanh::lean_inc(v_fst_6381_);
    leanh::lean_dec(v___x_6380_);
    if leanh::lean_obj_tag(v_fst_6381_) == 0 {
        let mut v___x_6382_: u8 = 0;
        v___x_6382_ = 0;
        return v___x_6382_;
    } else {
        let mut v_val_6383_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6384_: u8 = 0;
        v_val_6383_ = leanh::lean_ctor_get(v_fst_6381_, 0);
        leanh::lean_inc(v_val_6383_);
        leanh::lean_dec_ref_known(v_fst_6381_, 1);
        v___x_6384_ = (leanh::lean_unbox(v_val_6383_) as u8);
        leanh::lean_dec(v_val_6383_);
        return v___x_6384_;
    }
}
pub unsafe fn l_Vector_lex___redArg___boxed(
    mut v_n_6385_: *mut leanh::LeanObject,
    mut v_inst_6386_: *mut leanh::LeanObject,
    mut v_xs_6387_: *mut leanh::LeanObject,
    mut v_ys_6388_: *mut leanh::LeanObject,
    mut v_lt_6389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6390_: u8 = 0;
    let mut v_r_6391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6390_ =
        l_Vector_lex___redArg(v_n_6385_, v_inst_6386_, v_xs_6387_, v_ys_6388_, v_lt_6389_);
    v_r_6391_ = leanh::lean_box((v_res_6390_) as usize);
    return v_r_6391_;
}
pub unsafe fn l_Vector_lex(
    mut v_00_u03b1_6392_: *mut leanh::LeanObject,
    mut v_n_6393_: *mut leanh::LeanObject,
    mut v_inst_6394_: *mut leanh::LeanObject,
    mut v_xs_6395_: *mut leanh::LeanObject,
    mut v_ys_6396_: *mut leanh::LeanObject,
    mut v_lt_6397_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6398_: u8 = 0;
    v___x_6398_ =
        l_Vector_lex___redArg(v_n_6393_, v_inst_6394_, v_xs_6395_, v_ys_6396_, v_lt_6397_);
    return v___x_6398_;
}
pub unsafe fn l_Vector_lex___boxed(
    mut v_00_u03b1_6399_: *mut leanh::LeanObject,
    mut v_n_6400_: *mut leanh::LeanObject,
    mut v_inst_6401_: *mut leanh::LeanObject,
    mut v_xs_6402_: *mut leanh::LeanObject,
    mut v_ys_6403_: *mut leanh::LeanObject,
    mut v_lt_6404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6405_: u8 = 0;
    let mut v_r_6406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6405_ = l_Vector_lex(
        v_00_u03b1_6399_,
        v_n_6400_,
        v_inst_6401_,
        v_xs_6402_,
        v_ys_6403_,
        v_lt_6404_,
    );
    v_r_6406_ = leanh::lean_box((v_res_6405_) as usize);
    return v_r_6406_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Vector_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Nat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_InsertIdx(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_MapIdx(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Vector_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Vector_set___auto__1 = _init_l_Vector_set___auto__1();
    leanh::lean_mark_persistent(l_Vector_set___auto__1);
    l_Vector_swap___auto__1 = _init_l_Vector_swap___auto__1();
    leanh::lean_mark_persistent(l_Vector_swap___auto__1);
    l_Vector_swap___auto__3 = _init_l_Vector_swap___auto__3();
    leanh::lean_mark_persistent(l_Vector_swap___auto__3);
    l_Vector_swapAt___auto__1 = _init_l_Vector_swapAt___auto__1();
    leanh::lean_mark_persistent(l_Vector_swapAt___auto__1);
    l_Vector_eraseIdx___auto__1 = _init_l_Vector_eraseIdx___auto__1();
    leanh::lean_mark_persistent(l_Vector_eraseIdx___auto__1);
    l_Vector_insertIdx___auto__1 = _init_l_Vector_insertIdx___auto__1();
    leanh::lean_mark_persistent(l_Vector_insertIdx___auto__1);
    l_Vector_lex___auto__1 = _init_l_Vector_lex___auto__1();
    leanh::lean_mark_persistent(l_Vector_lex___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Vector_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Nat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_DecidableEq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_InsertIdx(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_MapIdx(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Vector_Basic(builtin);
}