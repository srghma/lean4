// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Context
// Imports: Lean.Elab.Tactic.Do.VCGen.Basic Lean.Elab.Tactic.Do.Internal.VCGen.SpecDB Lean.Meta.Sym.Apply Lean.Meta.Sym.Simp.DiscrTree Lean.Meta.Sym.Simp.SimpM Lean.Meta.Tactic.Grind.Types
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_instInhabitedPersistentArrayNode_default;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Attr::l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq;
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::SpecDB::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB,
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default,
    l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB,
};
use crate::r#gen::Lean::Elab::Tactic::Do::VCGen::Basic::{
    initialize_Lean_Elab_Tactic_Do_VCGen_Basic, runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Basic,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg;
use crate::r#gen::Lean::LocalContext::{l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_isAuxDecl};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp;
use crate::r#gen::Lean::Meta::DiscrTree::Basic::{
    l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes,
    l_Lean_Meta_DiscrTree_Key_lt, l_Lean_Meta_DiscrTree_instInhabited,
};
use crate::r#gen::Lean::Meta::DiscrTree::Types::{
    l_Lean_Meta_DiscrTree_Key_hash, l_Lean_Meta_DiscrTree_instBEqKey_beq,
};
use crate::r#gen::Lean::Meta::Sym::Apply::{
    initialize_Lean_Meta_Sym_Apply, runtime_initialize_Lean_Meta_Sym_Apply,
};
use crate::r#gen::Lean::Meta::Sym::Simp::DiscrTree::{
    initialize_Lean_Meta_Sym_Simp_DiscrTree, l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys,
    runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree,
};
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    initialize_Lean_Meta_Sym_Simp_SimpM, runtime_initialize_Lean_Meta_Sym_Simp_SimpM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_uget, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_12, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_usize, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3___closed__1_value) as *mut LeanObject;
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__4___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__4___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__0_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__1_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 105, 110, 115, 101, 114, 116, 75, 101, 121, 86, 97, 108, 117, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__2_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 107, 101, 121, 32, 115, 101, 113, 117, 101, 110, 99, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorIdx(
    mut v_x_1368_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1368_) {
        0 => {
            let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
            v___x_1369_ = lean_unsigned_to_nat(0);
            return v___x_1369_;
        }
        1 => {
            let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
            v___x_1370_ = lean_unsigned_to_nat(1);
            return v___x_1370_;
        }
        _ => {
            let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
            v___x_1371_ = lean_unsigned_to_nat(2);
            return v___x_1371_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorIdx___boxed(
    mut v_x_1372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1373_: *mut LeanObject = core::ptr::null_mut();
    v_res_1373_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorIdx(v_x_1372_);
    lean_dec(v_x_1372_);
    return v_res_1373_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(
    mut v_t_1374_: *mut LeanObject,
    mut v_k_1375_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_1374_) {
        0 => {
            return v_k_1375_;
        }
        1 => {
            let mut v_silent_1376_: u8 = 0;
            let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
            v_silent_1376_ = lean_ctor_get_uint8(v_t_1374_, 0 as u32);
            lean_dec_ref_known(v_t_1374_, 0);
            v___x_1377_ = lean_box((v_silent_1376_) as usize);
            v___x_1378_ = lean_apply_1(v_k_1375_, v___x_1377_);
            return v___x_1378_;
        }
        _ => {
            let mut v_tac_1379_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
            v_tac_1379_ = lean_ctor_get(v_t_1374_, 0);
            lean_inc(v_tac_1379_);
            lean_dec_ref_known(v_t_1374_, 1);
            v___x_1380_ = lean_apply_1(v_k_1375_, v_tac_1379_);
            return v___x_1380_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim(
    mut v_motive_1381_: *mut LeanObject,
    mut v_ctorIdx_1382_: *mut LeanObject,
    mut v_t_1383_: *mut LeanObject,
    mut v_h_1384_: *mut LeanObject,
    mut v_k_1385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    v___x_1386_ =
        l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_1383_, v_k_1385_);
    return v___x_1386_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___boxed(
    mut v_motive_1387_: *mut LeanObject,
    mut v_ctorIdx_1388_: *mut LeanObject,
    mut v_t_1389_: *mut LeanObject,
    mut v_h_1390_: *mut LeanObject,
    mut v_k_1391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1392_: *mut LeanObject = core::ptr::null_mut();
    v_res_1392_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim(
        v_motive_1387_,
        v_ctorIdx_1388_,
        v_t_1389_,
        v_h_1390_,
        v_k_1391_,
    );
    lean_dec(v_ctorIdx_1388_);
    return v_res_1392_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_none_elim___redArg(
    mut v_t_1393_: *mut LeanObject,
    mut v_none_1394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    v___x_1395_ =
        l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_1393_, v_none_1394_);
    return v___x_1395_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_none_elim(
    mut v_motive_1396_: *mut LeanObject,
    mut v_t_1397_: *mut LeanObject,
    mut v_h_1398_: *mut LeanObject,
    mut v_none_1399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    v___x_1400_ =
        l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_1397_, v_none_1399_);
    return v___x_1400_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_grind_elim___redArg(
    mut v_t_1401_: *mut LeanObject,
    mut v_grind_1402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    v___x_1403_ =
        l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_1401_, v_grind_1402_);
    return v___x_1403_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_grind_elim(
    mut v_motive_1404_: *mut LeanObject,
    mut v_t_1405_: *mut LeanObject,
    mut v_h_1406_: *mut LeanObject,
    mut v_grind_1407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    v___x_1408_ =
        l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_1405_, v_grind_1407_);
    return v___x_1408_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_tactic_elim___redArg(
    mut v_t_1409_: *mut LeanObject,
    mut v_tactic_1410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    v___x_1411_ =
        l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_1409_, v_tactic_1410_);
    return v___x_1411_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_tactic_elim(
    mut v_motive_1412_: *mut LeanObject,
    mut v_t_1413_: *mut LeanObject,
    mut v_h_1414_: *mut LeanObject,
    mut v_tactic_1415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    v___x_1416_ =
        l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_1413_, v_tactic_1415_);
    return v___x_1416_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_isGrind(
    mut v_x_1417_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_1417_) == 1 {
        let mut v___x_1418_: u8 = 0;
        v___x_1418_ = 1;
        return v___x_1418_;
    } else {
        let mut v___x_1419_: u8 = 0;
        v___x_1419_ = 0;
        return v___x_1419_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_isGrind___boxed(
    mut v_x_1420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1421_: u8 = 0;
    let mut v_r_1422_: *mut LeanObject = core::ptr::null_mut();
    v_res_1421_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_isGrind(v_x_1420_);
    lean_dec(v_x_1420_);
    v_r_1422_ = lean_box((v_res_1421_) as usize);
    return v_r_1422_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0()
-> *mut LeanObject {
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    v___x_1423_ = lean_unsigned_to_nat(0);
    v___x_1424_ = lean_box(1);
    v___x_1425_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default;
    v___x_1426_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1426_, 0, v___x_1425_);
    lean_ctor_set(v___x_1426_, 1, v___x_1424_);
    lean_ctor_set(v___x_1426_, 2, v___x_1423_);
    return v___x_1426_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default()
-> *mut LeanObject {
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    v___x_1427_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0,
    );
    return v___x_1427_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope() -> *mut LeanObject {
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    v___x_1428_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default;
    return v___x_1428_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_registerJP(
    mut v_s_1429_: *mut LeanObject,
    mut v_fv_1430_: *mut LeanObject,
    mut v_info_1431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_specs_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jps_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextDeclIdx_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1437_: u8 = 0;
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1442_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_specs_1432_ = lean_ctor_get(v_s_1429_, 0);
                v_jps_1433_ = lean_ctor_get(v_s_1429_, 1);
                v_nextDeclIdx_1434_ = lean_ctor_get(v_s_1429_, 2);
                v_isSharedCheck_1442_ = (!lean_is_exclusive(v_s_1429_)) as u8;
                if v_isSharedCheck_1442_ == 0 {
                    v___x_1436_ = v_s_1429_;
                    v_isShared_1437_ = v_isSharedCheck_1442_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nextDeclIdx_1434_);
                    lean_inc(v_jps_1433_);
                    lean_inc(v_specs_1432_);
                    lean_dec(v_s_1429_);
                    v___x_1436_ = lean_box(0);
                    v_isShared_1437_ = v_isSharedCheck_1442_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1438_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fv_1430_, v_info_1431_, v_jps_1433_);
                if v_isShared_1437_ == 0 {
                    lean_ctor_set(v___x_1436_, 1, v___x_1438_);
                    v___x_1440_ = v___x_1436_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_specs_1432_);
                    lean_ctor_set(v_reuseFailAlloc_1441_, 1, v___x_1438_);
                    lean_ctor_set(v_reuseFailAlloc_1441_, 2, v_nextDeclIdx_1434_);
                    v___x_1440_ = v_reuseFailAlloc_1441_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1440_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg(
    mut v_t_1443_: *mut LeanObject,
    mut v_k_1444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u8 = 0;
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1443_) == 0 {
                    v_k_1445_ = lean_ctor_get(v_t_1443_, 1);
                    v_v_1446_ = lean_ctor_get(v_t_1443_, 2);
                    v_l_1447_ = lean_ctor_get(v_t_1443_, 3);
                    v_r_1448_ = lean_ctor_get(v_t_1443_, 4);
                    v___x_1449_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1444_, v_k_1445_);
                    match v___x_1449_ {
                        0 => {
                            v_t_1443_ = v_l_1447_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_inc(v_v_1446_);
                            v___x_1451_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_1451_, 0, v_v_1446_);
                            return v___x_1451_;
                        }
                        _ => {
                            v_t_1443_ = v_r_1448_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1453_ = lean_box(0);
                    return v___x_1453_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg___boxed(
    mut v_t_1454_: *mut LeanObject,
    mut v_k_1455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1456_: *mut LeanObject = core::ptr::null_mut();
    v_res_1456_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_t_1454_, v_k_1455_);
    lean_dec(v_k_1455_);
    lean_dec(v_t_1454_);
    return v_res_1456_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f(
    mut v_s_1457_: *mut LeanObject,
    mut v_fv_1458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_jps_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    v_jps_1459_ = lean_ctor_get(v_s_1457_, 1);
    v___x_1460_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_jps_1459_, v_fv_1458_);
    return v___x_1460_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f___boxed(
    mut v_s_1461_: *mut LeanObject,
    mut v_fv_1462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1463_: *mut LeanObject = core::ptr::null_mut();
    v_res_1463_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f(v_s_1461_, v_fv_1462_);
    lean_dec(v_fv_1462_);
    lean_dec_ref(v_s_1461_);
    return v_res_1463_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0(
    mut v_00_u03b4_1464_: *mut LeanObject,
    mut v_t_1465_: *mut LeanObject,
    mut v_k_1466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    v___x_1467_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_t_1465_, v_k_1466_);
    return v___x_1467_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___boxed(
    mut v_00_u03b4_1468_: *mut LeanObject,
    mut v_t_1469_: *mut LeanObject,
    mut v_k_1470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1471_: *mut LeanObject = core::ptr::null_mut();
    v_res_1471_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0(v_00_u03b4_1468_, v_t_1469_, v_k_1470_);
    lean_dec(v_k_1470_);
    lean_dec(v_t_1469_);
    return v_res_1471_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__7_spec__9___redArg(
    mut v_x_1472_: *mut LeanObject,
    mut v_x_1473_: *mut LeanObject,
    mut v_x_1474_: *mut LeanObject,
    mut v_x_1475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1480_: u8 = 0;
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: u8 = 0;
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: u8 = 0;
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1501_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1476_ = lean_ctor_get(v_x_1472_, 0);
                v_vs_1477_ = lean_ctor_get(v_x_1472_, 1);
                v_isSharedCheck_1501_ = (!lean_is_exclusive(v_x_1472_)) as u8;
                if v_isSharedCheck_1501_ == 0 {
                    v___x_1479_ = v_x_1472_;
                    v_isShared_1480_ = v_isSharedCheck_1501_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_1477_);
                    lean_inc(v_ks_1476_);
                    lean_dec(v_x_1472_);
                    v___x_1479_ = lean_box(0);
                    v_isShared_1480_ = v_isSharedCheck_1501_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1481_ = lean_array_get_size(v_ks_1476_);
                v___x_1482_ = lean_nat_dec_lt(v_x_1473_, v___x_1481_);
                if v___x_1482_ == 0 {
                    lean_dec(v_x_1473_);
                    v___x_1483_ = lean_array_push(v_ks_1476_, v_x_1474_);
                    v___x_1484_ = lean_array_push(v_vs_1477_, v_x_1475_);
                    if v_isShared_1480_ == 0 {
                        lean_ctor_set(v___x_1479_, 1, v___x_1484_);
                        lean_ctor_set(v___x_1479_, 0, v___x_1483_);
                        v___x_1486_ = v___x_1479_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1483_);
                        lean_ctor_set(v_reuseFailAlloc_1487_, 1, v___x_1484_);
                        v___x_1486_ = v_reuseFailAlloc_1487_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1488_ = lean_array_fget_borrowed(v_ks_1476_, v_x_1473_);
                    v___x_1489_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1474_, v_k_x27_1488_);
                    if v___x_1489_ == 0 {
                        if v_isShared_1480_ == 0 {
                            v___x_1491_ = v___x_1479_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_ks_1476_);
                            lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_vs_1477_);
                            v___x_1491_ = v_reuseFailAlloc_1495_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1496_ = lean_array_fset(v_ks_1476_, v_x_1473_, v_x_1474_);
                        v___x_1497_ = lean_array_fset(v_vs_1477_, v_x_1473_, v_x_1475_);
                        lean_dec(v_x_1473_);
                        if v_isShared_1480_ == 0 {
                            lean_ctor_set(v___x_1479_, 1, v___x_1497_);
                            lean_ctor_set(v___x_1479_, 0, v___x_1496_);
                            v___x_1499_ = v___x_1479_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1496_);
                            lean_ctor_set(v_reuseFailAlloc_1500_, 1, v___x_1497_);
                            v___x_1499_ = v_reuseFailAlloc_1500_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1486_;
            }
            3 => {
                v___x_1492_ = lean_unsigned_to_nat(1);
                v___x_1493_ = lean_nat_add(v_x_1473_, v___x_1492_);
                lean_dec(v_x_1473_);
                v_x_1472_ = v___x_1491_;
                v_x_1473_ = v___x_1493_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1499_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(
    mut v_n_1502_: *mut LeanObject,
    mut v_k_1503_: *mut LeanObject,
    mut v_v_1504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    v___x_1505_ = lean_unsigned_to_nat(0);
    v___x_1506_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__7_spec__9___redArg(v_n_1502_, v___x_1505_, v_k_1503_, v_v_1504_);
    return v___x_1506_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_1507_: usize = 0;
    let mut v___x_1508_: usize = 0;
    let mut v___x_1509_: usize = 0;
    v___x_1507_ = 5usize;
    v___x_1508_ = 1usize;
    v___x_1509_ = lean_usize_shift_left(v___x_1508_, v___x_1507_);
    return v___x_1509_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_1510_: usize = 0;
    let mut v___x_1511_: usize = 0;
    let mut v___x_1512_: usize = 0;
    v___x_1510_ = 1usize;
    v___x_1511_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__0);
    v___x_1512_ = lean_usize_sub(v___x_1511_, v___x_1510_);
    return v___x_1512_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    v___x_1513_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_1513_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_x_1514_: *mut LeanObject,
    mut v_x_1515_: usize,
    mut v_x_1516_: usize,
    mut v_x_1517_: *mut LeanObject,
    mut v_x_1518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: usize = 0;
    let mut v___x_1521_: usize = 0;
    let mut v___x_1522_: usize = 0;
    let mut v___x_1523_: usize = 0;
    let mut v_j_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: u8 = 0;
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1529_: u8 = 0;
    let mut v_v_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1543_: u8 = 0;
    let mut v___x_1544_: u8 = 0;
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1550_: u8 = 0;
    let mut v_node_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1554_: u8 = 0;
    let mut v___x_1555_: usize = 0;
    let mut v___x_1556_: usize = 0;
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1561_: u8 = 0;
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1563_: u8 = 0;
    let mut v_unused_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1569_: u8 = 0;
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1574_: u8 = 0;
    let mut v_ks_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: usize = 0;
    let mut v___x_1581_: u8 = 0;
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: u8 = 0;
    let mut v_reuseFailAlloc_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1586_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1514_) == 0 {
                    v_es_1519_ = lean_ctor_get(v_x_1514_, 0);
                    v___x_1520_ = 5usize;
                    v___x_1521_ = 1usize;
                    v___x_1522_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__1);
                    v___x_1523_ = lean_usize_land(v_x_1515_, v___x_1522_);
                    v_j_1524_ = lean_usize_to_nat(v___x_1523_);
                    v___x_1525_ = lean_array_get_size(v_es_1519_);
                    v___x_1526_ = lean_nat_dec_lt(v_j_1524_, v___x_1525_);
                    if v___x_1526_ == 0 {
                        lean_dec(v_j_1524_);
                        lean_dec(v_x_1518_);
                        lean_dec(v_x_1517_);
                        return v_x_1514_;
                    } else {
                        lean_inc_ref(v_es_1519_);
                        v_isSharedCheck_1563_ = (!lean_is_exclusive(v_x_1514_)) as u8;
                        if v_isSharedCheck_1563_ == 0 {
                            v_unused_1564_ = lean_ctor_get(v_x_1514_, 0);
                            lean_dec(v_unused_1564_);
                            v___x_1528_ = v_x_1514_;
                            v_isShared_1529_ = v_isSharedCheck_1563_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_1514_);
                            v___x_1528_ = lean_box(0);
                            v_isShared_1529_ = v_isSharedCheck_1563_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1565_ = lean_ctor_get(v_x_1514_, 0);
                    v_vs_1566_ = lean_ctor_get(v_x_1514_, 1);
                    v_isSharedCheck_1586_ = (!lean_is_exclusive(v_x_1514_)) as u8;
                    if v_isSharedCheck_1586_ == 0 {
                        v___x_1568_ = v_x_1514_;
                        v_isShared_1569_ = v_isSharedCheck_1586_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_1566_);
                        lean_inc(v_ks_1565_);
                        lean_dec(v_x_1514_);
                        v___x_1568_ = lean_box(0);
                        v_isShared_1569_ = v_isSharedCheck_1586_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1530_ = lean_array_fget(v_es_1519_, v_j_1524_);
                v___x_1531_ = lean_box(0);
                v_xs_x27_1532_ = lean_array_fset(v_es_1519_, v_j_1524_, v___x_1531_);
                match lean_obj_tag(v_v_1530_) {
                    0 => {
                        v_key_1539_ = lean_ctor_get(v_v_1530_, 0);
                        v_val_1540_ = lean_ctor_get(v_v_1530_, 1);
                        v_isSharedCheck_1550_ = (!lean_is_exclusive(v_v_1530_)) as u8;
                        if v_isSharedCheck_1550_ == 0 {
                            v___x_1542_ = v_v_1530_;
                            v_isShared_1543_ = v_isSharedCheck_1550_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_1540_);
                            lean_inc(v_key_1539_);
                            lean_dec(v_v_1530_);
                            v___x_1542_ = lean_box(0);
                            v_isShared_1543_ = v_isSharedCheck_1550_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1551_ = lean_ctor_get(v_v_1530_, 0);
                        v_isSharedCheck_1561_ = (!lean_is_exclusive(v_v_1530_)) as u8;
                        if v_isSharedCheck_1561_ == 0 {
                            v___x_1553_ = v_v_1530_;
                            v_isShared_1554_ = v_isSharedCheck_1561_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_1551_);
                            lean_dec(v_v_1530_);
                            v___x_1553_ = lean_box(0);
                            v_isShared_1554_ = v_isSharedCheck_1561_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1562_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1562_, 0, v_x_1517_);
                        lean_ctor_set(v___x_1562_, 1, v_x_1518_);
                        v___y_1534_ = v___x_1562_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1535_ = lean_array_fset(v_xs_x27_1532_, v_j_1524_, v___y_1534_);
                lean_dec(v_j_1524_);
                if v_isShared_1529_ == 0 {
                    lean_ctor_set(v___x_1528_, 0, v___x_1535_);
                    v___x_1537_ = v___x_1528_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1535_);
                    v___x_1537_ = v_reuseFailAlloc_1538_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1537_;
            }
            4 => {
                v___x_1544_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1517_, v_key_1539_);
                if v___x_1544_ == 0 {
                    lean_del_object(v___x_1542_);
                    v___x_1545_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1539_,
                        v_val_1540_,
                        v_x_1517_,
                        v_x_1518_,
                    );
                    v___x_1546_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1546_, 0, v___x_1545_);
                    v___y_1534_ = v___x_1546_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_1540_);
                    lean_dec(v_key_1539_);
                    if v_isShared_1543_ == 0 {
                        lean_ctor_set(v___x_1542_, 1, v_x_1518_);
                        lean_ctor_set(v___x_1542_, 0, v_x_1517_);
                        v___x_1548_ = v___x_1542_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_x_1517_);
                        lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_x_1518_);
                        v___x_1548_ = v_reuseFailAlloc_1549_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1534_ = v___x_1548_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1555_ = lean_usize_shift_right(v_x_1515_, v___x_1520_);
                v___x_1556_ = lean_usize_add(v_x_1516_, v___x_1521_);
                v___x_1557_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg(v_node_1551_, v___x_1555_, v___x_1556_, v_x_1517_, v_x_1518_);
                if v_isShared_1554_ == 0 {
                    lean_ctor_set(v___x_1553_, 0, v___x_1557_);
                    v___x_1559_ = v___x_1553_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
                    v___x_1559_ = v_reuseFailAlloc_1560_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1534_ = v___x_1559_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1569_ == 0 {
                    v___x_1571_ = v___x_1568_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_ks_1565_);
                    lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_vs_1566_);
                    v___x_1571_ = v_reuseFailAlloc_1585_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1572_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v___x_1571_, v_x_1517_, v_x_1518_);
                v___x_1580_ = 7usize;
                v___x_1581_ = lean_usize_dec_le(v___x_1580_, v_x_1516_);
                if v___x_1581_ == 0 {
                    v___x_1582_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1572_);
                    v___x_1583_ = lean_unsigned_to_nat(4);
                    v___x_1584_ = lean_nat_dec_lt(v___x_1582_, v___x_1583_);
                    lean_dec(v___x_1582_);
                    v___y_1574_ = v___x_1584_;
                    state = 10;
                    continue;
                } else {
                    v___y_1574_ = v___x_1581_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1574_ == 0 {
                    v_ks_1575_ = lean_ctor_get(v_newNode_1572_, 0);
                    lean_inc_ref(v_ks_1575_);
                    v_vs_1576_ = lean_ctor_get(v_newNode_1572_, 1);
                    lean_inc_ref(v_vs_1576_);
                    lean_dec_ref(v_newNode_1572_);
                    v___x_1577_ = lean_unsigned_to_nat(0);
                    v___x_1578_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__2);
                    v___x_1579_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__8___redArg(v_x_1516_, v_ks_1575_, v_vs_1576_, v___x_1577_, v___x_1578_);
                    lean_dec_ref(v_vs_1576_);
                    lean_dec_ref(v_ks_1575_);
                    return v___x_1579_;
                } else {
                    return v_newNode_1572_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__8___redArg(
    mut v_depth_1587_: usize,
    mut v_keys_1588_: *mut LeanObject,
    mut v_vals_1589_: *mut LeanObject,
    mut v_i_1590_: *mut LeanObject,
    mut v_entries_1591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: u8 = 0;
    let mut v_k_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: u64 = 0;
    let mut v_h_1597_: usize = 0;
    let mut v___x_1598_: usize = 0;
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: usize = 0;
    let mut v___x_1601_: usize = 0;
    let mut v___x_1602_: usize = 0;
    let mut v_h_1603_: usize = 0;
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1592_ = lean_array_get_size(v_keys_1588_);
                v___x_1593_ = lean_nat_dec_lt(v_i_1590_, v___x_1592_);
                if v___x_1593_ == 0 {
                    lean_dec(v_i_1590_);
                    return v_entries_1591_;
                } else {
                    v_k_1594_ = lean_array_fget_borrowed(v_keys_1588_, v_i_1590_);
                    v_v_1595_ = lean_array_fget_borrowed(v_vals_1589_, v_i_1590_);
                    v___x_1596_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_1594_);
                    v_h_1597_ = lean_uint64_to_usize(v___x_1596_);
                    v___x_1598_ = 5usize;
                    v___x_1599_ = lean_unsigned_to_nat(1);
                    v___x_1600_ = 1usize;
                    v___x_1601_ = lean_usize_sub(v_depth_1587_, v___x_1600_);
                    v___x_1602_ = lean_usize_mul(v___x_1598_, v___x_1601_);
                    v_h_1603_ = lean_usize_shift_right(v_h_1597_, v___x_1602_);
                    v___x_1604_ = lean_nat_add(v_i_1590_, v___x_1599_);
                    lean_dec(v_i_1590_);
                    lean_inc(v_v_1595_);
                    lean_inc(v_k_1594_);
                    v___x_1605_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg(v_entries_1591_, v_h_1603_, v_depth_1587_, v_k_1594_, v_v_1595_);
                    v_i_1590_ = v___x_1604_;
                    v_entries_1591_ = v___x_1605_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__8___redArg___boxed(
    mut v_depth_1607_: *mut LeanObject,
    mut v_keys_1608_: *mut LeanObject,
    mut v_vals_1609_: *mut LeanObject,
    mut v_i_1610_: *mut LeanObject,
    mut v_entries_1611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1612_: usize = 0;
    let mut v_res_1613_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1612_ = lean_unbox_usize(v_depth_1607_);
    lean_dec(v_depth_1607_);
    v_res_1613_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__8___redArg(v_depth_boxed_1612_, v_keys_1608_, v_vals_1609_, v_i_1610_, v_entries_1611_);
    lean_dec_ref(v_vals_1609_);
    lean_dec_ref(v_keys_1608_);
    return v_res_1613_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_x_1614_: *mut LeanObject,
    mut v_x_1615_: *mut LeanObject,
    mut v_x_1616_: *mut LeanObject,
    mut v_x_1617_: *mut LeanObject,
    mut v_x_1618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1621__boxed_1619_: usize = 0;
    let mut v_x_1622__boxed_1620_: usize = 0;
    let mut v_res_1621_: *mut LeanObject = core::ptr::null_mut();
    v_x_1621__boxed_1619_ = lean_unbox_usize(v_x_1615_);
    lean_dec(v_x_1615_);
    v_x_1622__boxed_1620_ = lean_unbox_usize(v_x_1616_);
    lean_dec(v_x_1616_);
    v_res_1621_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg(v_x_1614_, v_x_1621__boxed_1619_, v_x_1622__boxed_1620_, v_x_1617_, v_x_1618_);
    return v_res_1621_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2___redArg(
    mut v_x_1622_: *mut LeanObject,
    mut v_x_1623_: *mut LeanObject,
    mut v_x_1624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1625_: u64 = 0;
    let mut v___x_1626_: usize = 0;
    let mut v___x_1627_: usize = 0;
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    v___x_1625_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1623_);
    v___x_1626_ = lean_uint64_to_usize(v___x_1625_);
    v___x_1627_ = 1usize;
    v___x_1628_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg(v_x_1622_, v___x_1626_, v___x_1627_, v_x_1623_, v_x_1624_);
    return v___x_1628_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__0(
    mut v_x_1629_: *mut LeanObject,
    mut v_keys_1630_: *mut LeanObject,
    mut v_v_1631_: *mut LeanObject,
    mut v_k_1632_: *mut LeanObject,
    mut v_x_1633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    v___x_1634_ = lean_unsigned_to_nat(1);
    v___x_1635_ = lean_nat_add(v_x_1629_, v___x_1634_);
    v_c_1636_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
        lean_box(0),
        v_keys_1630_,
        v_v_1631_,
        v___x_1635_,
    );
    lean_dec(v___x_1635_);
    v___x_1637_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1637_, 0, v_k_1632_);
    lean_ctor_set(v___x_1637_, 1, v_c_1636_);
    return v___x_1637_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__0___boxed(
    mut v_x_1638_: *mut LeanObject,
    mut v_keys_1639_: *mut LeanObject,
    mut v_v_1640_: *mut LeanObject,
    mut v_k_1641_: *mut LeanObject,
    mut v_x_1642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1643_: *mut LeanObject = core::ptr::null_mut();
    v_res_1643_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__0(v_x_1638_, v_keys_1639_, v_v_1640_, v_k_1641_, v_x_1642_);
    lean_dec_ref(v_keys_1639_);
    lean_dec(v_x_1638_);
    return v_res_1643_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__1(
    mut v_a_1644_: *mut LeanObject,
    mut v_b_1645_: *mut LeanObject,
) -> u8 {
    let mut v_fst_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: u8 = 0;
    v_fst_1646_ = lean_ctor_get(v_a_1644_, 0);
    v_fst_1647_ = lean_ctor_get(v_b_1645_, 0);
    v___x_1648_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1646_, v_fst_1647_);
    return v___x_1648_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__1___boxed(
    mut v_a_1649_: *mut LeanObject,
    mut v_b_1650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1651_: u8 = 0;
    let mut v_r_1652_: *mut LeanObject = core::ptr::null_mut();
    v_res_1651_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__1(v_a_1649_, v_b_1650_);
    lean_dec_ref(v_b_1650_);
    lean_dec_ref(v_a_1649_);
    v_r_1652_ = lean_box((v_res_1651_) as usize);
    return v_r_1652_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__6_spec__11(
    mut v_vs_1653_: *mut LeanObject,
    mut v_v_1654_: *mut LeanObject,
    mut v_i_1655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: u8 = 0;
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: u8 = 0;
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1656_ = lean_array_get_size(v_vs_1653_);
                v___x_1657_ = lean_nat_dec_lt(v_i_1655_, v___x_1656_);
                if v___x_1657_ == 0 {
                    lean_dec(v_i_1655_);
                    v___x_1658_ = lean_array_push(v_vs_1653_, v_v_1654_);
                    return v___x_1658_;
                } else {
                    v_proof_1659_ = lean_ctor_get(v_v_1654_, 1);
                    v___x_1660_ = lean_array_fget_borrowed(v_vs_1653_, v_i_1655_);
                    v_proof_1661_ = lean_ctor_get(v___x_1660_, 1);
                    lean_inc_ref(v_proof_1661_);
                    lean_inc_ref(v_proof_1659_);
                    v___x_1662_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(
                        v_proof_1659_,
                        v_proof_1661_,
                    );
                    if v___x_1662_ == 0 {
                        v___x_1663_ = lean_unsigned_to_nat(1);
                        v___x_1664_ = lean_nat_add(v_i_1655_, v___x_1663_);
                        lean_dec(v_i_1655_);
                        v_i_1655_ = v___x_1664_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1666_ = lean_array_fset(v_vs_1653_, v_i_1655_, v_v_1654_);
                        lean_dec(v_i_1655_);
                        return v___x_1666_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__6(
    mut v_vs_1667_: *mut LeanObject,
    mut v_v_1668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    v___x_1669_ = lean_unsigned_to_nat(0);
    v___x_1670_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__6_spec__11(v_vs_1667_, v_v_1668_, v___x_1669_);
    return v___x_1670_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7_spec__13___redArg(
    mut v_x_1675_: *mut LeanObject,
    mut v_keys_1676_: *mut LeanObject,
    mut v_v_1677_: *mut LeanObject,
    mut v_k_1678_: *mut LeanObject,
    mut v_as_1679_: *mut LeanObject,
    mut v_k_1680_: *mut LeanObject,
    mut v_x_1681_: *mut LeanObject,
    mut v_x_1682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_midVal_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: u8 = 0;
    let mut v___x_1688_: u8 = 0;
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: u8 = 0;
    let mut v_snd_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1694_: u8 = 0;
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1703_: u8 = 0;
    let mut v_unused_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: u8 = 0;
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_as_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1683_ = lean_nat_add(v_x_1681_, v_x_1682_);
                v___x_1684_ = lean_unsigned_to_nat(1);
                v_mid_1685_ = lean_nat_shiftr(v___x_1683_, v___x_1684_);
                lean_dec(v___x_1683_);
                v_midVal_1686_ = lean_array_fget(v_as_1679_, v_mid_1685_);
                v___x_1687_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__1(v_midVal_1686_, v_k_1680_);
                if v___x_1687_ == 0 {
                    lean_dec(v_x_1682_);
                    v___x_1688_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__1(v_k_1680_, v_midVal_1686_);
                    if v___x_1688_ == 0 {
                        lean_dec(v_x_1681_);
                        v___x_1689_ = lean_array_get_size(v_as_1679_);
                        v___x_1690_ = lean_nat_dec_lt(v_mid_1685_, v___x_1689_);
                        if v___x_1690_ == 0 {
                            lean_dec(v_midVal_1686_);
                            lean_dec(v_mid_1685_);
                            lean_dec(v_k_1678_);
                            lean_dec_ref(v_v_1677_);
                            return v_as_1679_;
                        } else {
                            v_snd_1691_ = lean_ctor_get(v_midVal_1686_, 1);
                            v_isSharedCheck_1703_ = (!lean_is_exclusive(v_midVal_1686_)) as u8;
                            if v_isSharedCheck_1703_ == 0 {
                                v_unused_1704_ = lean_ctor_get(v_midVal_1686_, 0);
                                lean_dec(v_unused_1704_);
                                v___x_1693_ = v_midVal_1686_;
                                v_isShared_1694_ = v_isSharedCheck_1703_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_snd_1691_);
                                lean_dec(v_midVal_1686_);
                                v___x_1693_ = lean_box(0);
                                v_isShared_1694_ = v_isSharedCheck_1703_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_midVal_1686_);
                        v_x_1682_ = v_mid_1685_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec(v_midVal_1686_);
                    v___x_1706_ = lean_nat_dec_eq(v_mid_1685_, v_x_1681_);
                    if v___x_1706_ == 0 {
                        lean_dec(v_x_1681_);
                        v_x_1681_ = v_mid_1685_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_mid_1685_);
                        lean_dec(v_x_1682_);
                        v___x_1708_ = lean_nat_add(v_x_1675_, v___x_1684_);
                        v_c_1709_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_1676_, v_v_1677_, v___x_1708_);
                        lean_dec(v___x_1708_);
                        v___x_1710_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1710_, 0, v_k_1678_);
                        lean_ctor_set(v___x_1710_, 1, v_c_1709_);
                        v___x_1711_ = lean_nat_add(v_x_1681_, v___x_1684_);
                        lean_dec(v_x_1681_);
                        v_j_1712_ = lean_array_get_size(v_as_1679_);
                        v_as_1713_ = lean_array_push(v_as_1679_, v___x_1710_);
                        v___x_1714_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                            lean_box(0),
                            v___x_1711_,
                            v_as_1713_,
                            v_j_1712_,
                        );
                        lean_dec(v___x_1711_);
                        return v___x_1714_;
                    }
                }
            }
            1 => {
                v___x_1695_ = lean_box(0);
                v_xs_x27_1696_ = lean_array_fset(v_as_1679_, v_mid_1685_, v___x_1695_);
                v___x_1697_ = lean_nat_add(v_x_1675_, v___x_1684_);
                v_c_1698_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3(v_keys_1676_, v_v_1677_, v___x_1697_, v_snd_1691_);
                lean_dec(v___x_1697_);
                if v_isShared_1694_ == 0 {
                    lean_ctor_set(v___x_1693_, 1, v_c_1698_);
                    lean_ctor_set(v___x_1693_, 0, v_k_1678_);
                    v___x_1700_ = v___x_1693_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_k_1678_);
                    lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_c_1698_);
                    v___x_1700_ = v_reuseFailAlloc_1702_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1701_ = lean_array_fset(v_xs_x27_1696_, v_mid_1685_, v___x_1700_);
                lean_dec(v_mid_1685_);
                return v___x_1701_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7(
    mut v_x_1715_: *mut LeanObject,
    mut v_keys_1716_: *mut LeanObject,
    mut v_v_1717_: *mut LeanObject,
    mut v_k_1718_: *mut LeanObject,
    mut v_as_1719_: *mut LeanObject,
    mut v_k_1720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: u8 = 0;
    v___x_1721_ = lean_array_get_size(v_as_1719_);
    v___x_1722_ = lean_unsigned_to_nat(0);
    v___x_1723_ = lean_nat_dec_eq(v___x_1721_, v___x_1722_);
    if v___x_1723_ == 0 {
        let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1725_: u8 = 0;
        v___x_1724_ = lean_array_fget_borrowed(v_as_1719_, v___x_1722_);
        v___x_1725_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__1(v_k_1720_, v___x_1724_);
        if v___x_1725_ == 0 {
            let mut v___x_1726_: u8 = 0;
            v___x_1726_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__1(v___x_1724_, v_k_1720_);
            if v___x_1726_ == 0 {
                let mut v___x_1727_: u8 = 0;
                v___x_1727_ = lean_nat_dec_lt(v___x_1722_, v___x_1721_);
                if v___x_1727_ == 0 {
                    lean_dec(v_k_1718_);
                    lean_dec_ref(v_v_1717_);
                    return v_as_1719_;
                } else {
                    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_xs_x27_1729_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
                    lean_inc(v___x_1724_);
                    v___x_1728_ = lean_box(0);
                    v_xs_x27_1729_ = lean_array_fset(v_as_1719_, v___x_1722_, v___x_1728_);
                    v___x_1730_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__2(v_x_1715_, v_keys_1716_, v_v_1717_, v_k_1718_, v___x_1724_);
                    v___x_1731_ = lean_array_fset(v_xs_x27_1729_, v___x_1722_, v___x_1730_);
                    return v___x_1731_;
                }
            } else {
                let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1735_: u8 = 0;
                v___x_1732_ = lean_unsigned_to_nat(1);
                v___x_1733_ = lean_nat_sub(v___x_1721_, v___x_1732_);
                v___x_1734_ = lean_array_fget_borrowed(v_as_1719_, v___x_1733_);
                v___x_1735_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__1(v___x_1734_, v_k_1720_);
                if v___x_1735_ == 0 {
                    let mut v___x_1736_: u8 = 0;
                    v___x_1736_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__1(v_k_1720_, v___x_1734_);
                    if v___x_1736_ == 0 {
                        let mut v___x_1737_: u8 = 0;
                        v___x_1737_ = lean_nat_dec_lt(v___x_1733_, v___x_1721_);
                        if v___x_1737_ == 0 {
                            lean_dec(v___x_1733_);
                            lean_dec(v_k_1718_);
                            lean_dec_ref(v_v_1717_);
                            return v_as_1719_;
                        } else {
                            let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_xs_x27_1739_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
                            lean_inc(v___x_1734_);
                            v___x_1738_ = lean_box(0);
                            v_xs_x27_1739_ = lean_array_fset(v_as_1719_, v___x_1733_, v___x_1738_);
                            v___x_1740_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__2(v_x_1715_, v_keys_1716_, v_v_1717_, v_k_1718_, v___x_1734_);
                            v___x_1741_ = lean_array_fset(v_xs_x27_1739_, v___x_1733_, v___x_1740_);
                            lean_dec(v___x_1733_);
                            return v___x_1741_;
                        }
                    } else {
                        let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
                        v___x_1742_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7_spec__13___redArg(v_x_1715_, v_keys_1716_, v_v_1717_, v_k_1718_, v_as_1719_, v_k_1720_, v___x_1722_, v___x_1733_);
                        return v___x_1742_;
                    }
                } else {
                    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v___x_1733_);
                    v___x_1743_ = lean_box(0);
                    v___x_1744_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__0(v_x_1715_, v_keys_1716_, v_v_1717_, v_k_1718_, v___x_1743_);
                    v___x_1745_ = lean_array_push(v_as_1719_, v___x_1744_);
                    return v___x_1745_;
                }
            }
        } else {
            let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
            let mut v_as_1748_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
            v___x_1746_ = lean_box(0);
            v___x_1747_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__0(v_x_1715_, v_keys_1716_, v_v_1717_, v_k_1718_, v___x_1746_);
            v_as_1748_ = lean_array_push(v_as_1719_, v___x_1747_);
            v___x_1749_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                lean_box(0),
                v___x_1722_,
                v_as_1748_,
                v___x_1721_,
            );
            return v___x_1749_;
        }
    } else {
        let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
        v___x_1750_ = lean_box(0);
        v___x_1751_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__0(v_x_1715_, v_keys_1716_, v_v_1717_, v_k_1718_, v___x_1750_);
        v___x_1752_ = lean_array_push(v_as_1719_, v___x_1751_);
        return v___x_1752_;
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3(
    mut v_keys_1753_: *mut LeanObject,
    mut v_v_1754_: *mut LeanObject,
    mut v_x_1755_: *mut LeanObject,
    mut v_x_1756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vs_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1761_: u8 = 0;
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1775_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vs_1757_ = lean_ctor_get(v_x_1756_, 0);
                v_children_1758_ = lean_ctor_get(v_x_1756_, 1);
                v_isSharedCheck_1775_ = (!lean_is_exclusive(v_x_1756_)) as u8;
                if v_isSharedCheck_1775_ == 0 {
                    v___x_1760_ = v_x_1756_;
                    v_isShared_1761_ = v_isSharedCheck_1775_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_children_1758_);
                    lean_inc(v_vs_1757_);
                    lean_dec(v_x_1756_);
                    v___x_1760_ = lean_box(0);
                    v_isShared_1761_ = v_isSharedCheck_1775_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1762_ = lean_array_get_size(v_keys_1753_);
                v___x_1763_ = lean_nat_dec_lt(v_x_1755_, v___x_1762_);
                if v___x_1763_ == 0 {
                    v___x_1764_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__6(v_vs_1757_, v_v_1754_);
                    if v_isShared_1761_ == 0 {
                        lean_ctor_set(v___x_1760_, 0, v___x_1764_);
                        v___x_1766_ = v___x_1760_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
                        lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_children_1758_);
                        v___x_1766_ = v_reuseFailAlloc_1767_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_1768_ = lean_array_fget_borrowed(v_keys_1753_, v_x_1755_);
                    v___x_1769_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3___closed__1;
                    lean_inc_n(v_k_1768_, 2);
                    v___x_1770_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1770_, 0, v_k_1768_);
                    lean_ctor_set(v___x_1770_, 1, v___x_1769_);
                    v_c_1771_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7(v_x_1755_, v_keys_1753_, v_v_1754_, v_k_1768_, v_children_1758_, v___x_1770_);
                    lean_dec_ref_known(v___x_1770_, 2);
                    if v_isShared_1761_ == 0 {
                        lean_ctor_set(v___x_1760_, 1, v_c_1771_);
                        v___x_1773_ = v___x_1760_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_vs_1757_);
                        lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_c_1771_);
                        v___x_1773_ = v_reuseFailAlloc_1774_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1766_;
            }
            3 => {
                return v___x_1773_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__2(
    mut v_x_1776_: *mut LeanObject,
    mut v_keys_1777_: *mut LeanObject,
    mut v_v_1778_: *mut LeanObject,
    mut v_k_1779_: *mut LeanObject,
    mut v_x_1780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1784_: u8 = 0;
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1791_: u8 = 0;
    let mut v_unused_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_1781_ = lean_ctor_get(v_x_1780_, 1);
                v_isSharedCheck_1791_ = (!lean_is_exclusive(v_x_1780_)) as u8;
                if v_isSharedCheck_1791_ == 0 {
                    v_unused_1792_ = lean_ctor_get(v_x_1780_, 0);
                    lean_dec(v_unused_1792_);
                    v___x_1783_ = v_x_1780_;
                    v_isShared_1784_ = v_isSharedCheck_1791_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1781_);
                    lean_dec(v_x_1780_);
                    v___x_1783_ = lean_box(0);
                    v_isShared_1784_ = v_isSharedCheck_1791_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1785_ = lean_unsigned_to_nat(1);
                v___x_1786_ = lean_nat_add(v_x_1776_, v___x_1785_);
                v_c_1787_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3(v_keys_1777_, v_v_1778_, v___x_1786_, v_snd_1781_);
                lean_dec(v___x_1786_);
                if v_isShared_1784_ == 0 {
                    lean_ctor_set(v___x_1783_, 1, v_c_1787_);
                    lean_ctor_set(v___x_1783_, 0, v_k_1779_);
                    v___x_1789_ = v___x_1783_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_k_1779_);
                    lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_c_1787_);
                    v___x_1789_ = v_reuseFailAlloc_1790_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1789_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__2___boxed(
    mut v_x_1793_: *mut LeanObject,
    mut v_keys_1794_: *mut LeanObject,
    mut v_v_1795_: *mut LeanObject,
    mut v_k_1796_: *mut LeanObject,
    mut v_x_1797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1798_: *mut LeanObject = core::ptr::null_mut();
    v_res_1798_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__2(v_x_1793_, v_keys_1794_, v_v_1795_, v_k_1796_, v_x_1797_);
    lean_dec_ref(v_keys_1794_);
    lean_dec(v_x_1793_);
    return v_res_1798_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3___boxed(
    mut v_keys_1799_: *mut LeanObject,
    mut v_v_1800_: *mut LeanObject,
    mut v_x_1801_: *mut LeanObject,
    mut v_x_1802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1803_: *mut LeanObject = core::ptr::null_mut();
    v_res_1803_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3(v_keys_1799_, v_v_1800_, v_x_1801_, v_x_1802_);
    lean_dec(v_x_1801_);
    lean_dec_ref(v_keys_1799_);
    return v_res_1803_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7_spec__13___redArg___boxed(
    mut v_x_1804_: *mut LeanObject,
    mut v_keys_1805_: *mut LeanObject,
    mut v_v_1806_: *mut LeanObject,
    mut v_k_1807_: *mut LeanObject,
    mut v_as_1808_: *mut LeanObject,
    mut v_k_1809_: *mut LeanObject,
    mut v_x_1810_: *mut LeanObject,
    mut v_x_1811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1812_: *mut LeanObject = core::ptr::null_mut();
    v_res_1812_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7_spec__13___redArg(v_x_1804_, v_keys_1805_, v_v_1806_, v_k_1807_, v_as_1808_, v_k_1809_, v_x_1810_, v_x_1811_);
    lean_dec_ref(v_k_1809_);
    lean_dec_ref(v_keys_1805_);
    lean_dec(v_x_1804_);
    return v_res_1812_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___boxed(
    mut v_x_1813_: *mut LeanObject,
    mut v_keys_1814_: *mut LeanObject,
    mut v_v_1815_: *mut LeanObject,
    mut v_k_1816_: *mut LeanObject,
    mut v_as_1817_: *mut LeanObject,
    mut v_k_1818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1819_: *mut LeanObject = core::ptr::null_mut();
    v_res_1819_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7(v_x_1813_, v_keys_1814_, v_v_1815_, v_k_1816_, v_as_1817_, v_k_1818_);
    lean_dec_ref(v_k_1818_);
    lean_dec_ref(v_keys_1814_);
    lean_dec(v_x_1813_);
    return v_res_1819_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__4___closed__0()
-> *mut LeanObject {
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    v___x_1820_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
    return v___x_1820_;
}
pub unsafe fn l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__4(
    mut v_msg_1821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    v___x_1822_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__4___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__4___closed__0_once), _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__4___closed__0);
    v___x_1823_ = lean_panic_fn_borrowed(v___x_1822_, v_msg_1821_);
    return v___x_1823_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_keys_1824_: *mut LeanObject,
    mut v_vals_1825_: *mut LeanObject,
    mut v_i_1826_: *mut LeanObject,
    mut v_k_1827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: u8 = 0;
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: u8 = 0;
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1828_ = lean_array_get_size(v_keys_1824_);
                v___x_1829_ = lean_nat_dec_lt(v_i_1826_, v___x_1828_);
                if v___x_1829_ == 0 {
                    lean_dec(v_i_1826_);
                    v___x_1830_ = lean_box(0);
                    return v___x_1830_;
                } else {
                    v_k_x27_1831_ = lean_array_fget_borrowed(v_keys_1824_, v_i_1826_);
                    v___x_1832_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_1827_, v_k_x27_1831_);
                    if v___x_1832_ == 0 {
                        v___x_1833_ = lean_unsigned_to_nat(1);
                        v___x_1834_ = lean_nat_add(v_i_1826_, v___x_1833_);
                        lean_dec(v_i_1826_);
                        v_i_1826_ = v___x_1834_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1836_ = lean_array_fget_borrowed(v_vals_1825_, v_i_1826_);
                        lean_dec(v_i_1826_);
                        lean_inc(v___x_1836_);
                        v___x_1837_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1837_, 0, v___x_1836_);
                        return v___x_1837_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_keys_1838_: *mut LeanObject,
    mut v_vals_1839_: *mut LeanObject,
    mut v_i_1840_: *mut LeanObject,
    mut v_k_1841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1842_: *mut LeanObject = core::ptr::null_mut();
    v_res_1842_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_keys_1838_, v_vals_1839_, v_i_1840_, v_k_1841_);
    lean_dec(v_k_1841_);
    lean_dec_ref(v_vals_1839_);
    lean_dec_ref(v_keys_1838_);
    return v_res_1842_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_1843_: *mut LeanObject,
    mut v_x_1844_: usize,
    mut v_x_1845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: usize = 0;
    let mut v___x_1849_: usize = 0;
    let mut v___x_1850_: usize = 0;
    let mut v_j_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: u8 = 0;
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: usize = 0;
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1843_) == 0 {
                    v_es_1846_ = lean_ctor_get(v_x_1843_, 0);
                    v___x_1847_ = lean_box(2);
                    v___x_1848_ = 5usize;
                    v___x_1849_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__1);
                    v___x_1850_ = lean_usize_land(v_x_1844_, v___x_1849_);
                    v_j_1851_ = lean_usize_to_nat(v___x_1850_);
                    v___x_1852_ = lean_array_get_borrowed(v___x_1847_, v_es_1846_, v_j_1851_);
                    lean_dec(v_j_1851_);
                    match lean_obj_tag(v___x_1852_) {
                        0 => {
                            v_key_1853_ = lean_ctor_get(v___x_1852_, 0);
                            v_val_1854_ = lean_ctor_get(v___x_1852_, 1);
                            v___x_1855_ =
                                l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1845_, v_key_1853_);
                            if v___x_1855_ == 0 {
                                v___x_1856_ = lean_box(0);
                                return v___x_1856_;
                            } else {
                                lean_inc(v_val_1854_);
                                v___x_1857_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_1857_, 0, v_val_1854_);
                                return v___x_1857_;
                            }
                        }
                        1 => {
                            v_node_1858_ = lean_ctor_get(v___x_1852_, 0);
                            v___x_1859_ = lean_usize_shift_right(v_x_1844_, v___x_1848_);
                            v_x_1843_ = v_node_1858_;
                            v_x_1844_ = v___x_1859_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1861_ = lean_box(0);
                            return v___x_1861_;
                        }
                    }
                } else {
                    v_ks_1862_ = lean_ctor_get(v_x_1843_, 0);
                    v_vs_1863_ = lean_ctor_get(v_x_1843_, 1);
                    v___x_1864_ = lean_unsigned_to_nat(0);
                    v___x_1865_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ks_1862_, v_vs_1863_, v___x_1864_, v_x_1845_);
                    return v___x_1865_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_x_1866_: *mut LeanObject,
    mut v_x_1867_: *mut LeanObject,
    mut v_x_1868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2068__boxed_1869_: usize = 0;
    let mut v_res_1870_: *mut LeanObject = core::ptr::null_mut();
    v_x_2068__boxed_1869_ = lean_unbox_usize(v_x_1867_);
    lean_dec(v_x_1867_);
    v_res_1870_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1866_, v_x_2068__boxed_1869_, v_x_1868_);
    lean_dec(v_x_1868_);
    lean_dec_ref(v_x_1866_);
    return v_res_1870_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1___redArg(
    mut v_x_1871_: *mut LeanObject,
    mut v_x_1872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1873_: u64 = 0;
    let mut v___x_1874_: usize = 0;
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    v___x_1873_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1872_);
    v___x_1874_ = lean_uint64_to_usize(v___x_1873_);
    v___x_1875_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1871_, v___x_1874_, v_x_1872_);
    return v___x_1875_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_1876_: *mut LeanObject,
    mut v_x_1877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1878_: *mut LeanObject = core::ptr::null_mut();
    v_res_1878_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1___redArg(v_x_1876_, v_x_1877_);
    lean_dec(v_x_1877_);
    lean_dec_ref(v_x_1876_);
    return v_res_1878_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    v___x_1882_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__2;
    v___x_1883_ = lean_unsigned_to_nat(23);
    v___x_1884_ = lean_unsigned_to_nat(166);
    v___x_1885_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__1;
    v___x_1886_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__0;
    v___x_1887_ = l_mkPanicMessageWithDecl(
        v___x_1886_,
        v___x_1885_,
        v___x_1884_,
        v___x_1883_,
        v___x_1882_,
    );
    return v___x_1887_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0(
    mut v_d_1888_: *mut LeanObject,
    mut v_keys_1889_: *mut LeanObject,
    mut v_v_1890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: u8 = 0;
    v___x_1891_ = lean_array_get_size(v_keys_1889_);
    v___x_1892_ = lean_unsigned_to_nat(0);
    v___x_1893_ = lean_nat_dec_eq(v___x_1891_, v___x_1892_);
    if v___x_1893_ == 0 {
        let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1895_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
        v___x_1894_ = lean_box(0);
        v_k_1895_ = lean_array_get_borrowed(v___x_1894_, v_keys_1889_, v___x_1892_);
        v___x_1896_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1___redArg(v_d_1888_, v_k_1895_);
        if lean_obj_tag(v___x_1896_) == 0 {
            let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_1898_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
            v___x_1897_ = lean_unsigned_to_nat(1);
            v_c_1898_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
                lean_box(0),
                v_keys_1889_,
                v_v_1890_,
                v___x_1897_,
            );
            lean_inc(v_k_1895_);
            v___x_1899_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2___redArg(v_d_1888_, v_k_1895_, v_c_1898_);
            return v___x_1899_;
        } else {
            let mut v_val_1900_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_1902_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
            v_val_1900_ = lean_ctor_get(v___x_1896_, 0);
            lean_inc(v_val_1900_);
            lean_dec_ref_known(v___x_1896_, 1);
            v___x_1901_ = lean_unsigned_to_nat(1);
            v_c_1902_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3(v_keys_1889_, v_v_1890_, v___x_1901_, v_val_1900_);
            lean_inc(v_k_1895_);
            v___x_1903_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2___redArg(v_d_1888_, v_k_1895_, v_c_1902_);
            return v___x_1903_;
        }
    } else {
        let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_v_1890_);
        lean_dec_ref(v_d_1888_);
        v___x_1904_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__3_once), _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__3);
        v___x_1905_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__4(v___x_1904_);
        return v___x_1905_;
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___boxed(
    mut v_d_1906_: *mut LeanObject,
    mut v_keys_1907_: *mut LeanObject,
    mut v_v_1908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1909_: *mut LeanObject = core::ptr::null_mut();
    v_res_1909_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0(v_d_1906_, v_keys_1907_, v_v_1908_);
    lean_dec_ref(v_keys_1907_);
    return v_res_1909_;
}
pub unsafe fn l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0(
    mut v_d_1910_: *mut LeanObject,
    mut v_p_1911_: *mut LeanObject,
    mut v_v_1912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_keys_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    v_keys_1913_ = l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(v_p_1911_);
    v___x_1914_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0(v_d_1910_, v_keys_1913_, v_v_1912_);
    lean_dec_ref(v_keys_1913_);
    return v___x_1914_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec(
    mut v_s_1915_: *mut LeanObject,
    mut v_thm_1916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_specs_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jps_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextDeclIdx_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v_specs_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_erased_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1927_: u8 = 0;
    let mut v_pattern_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1936_: u8 = 0;
    let mut v_isSharedCheck_1937_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_specs_1917_ = lean_ctor_get(v_s_1915_, 0);
                v_jps_1918_ = lean_ctor_get(v_s_1915_, 1);
                v_nextDeclIdx_1919_ = lean_ctor_get(v_s_1915_, 2);
                v_isSharedCheck_1937_ = (!lean_is_exclusive(v_s_1915_)) as u8;
                if v_isSharedCheck_1937_ == 0 {
                    v___x_1921_ = v_s_1915_;
                    v_isShared_1922_ = v_isSharedCheck_1937_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nextDeclIdx_1919_);
                    lean_inc(v_jps_1918_);
                    lean_inc(v_specs_1917_);
                    lean_dec(v_s_1915_);
                    v___x_1921_ = lean_box(0);
                    v_isShared_1922_ = v_isSharedCheck_1937_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_specs_1923_ = lean_ctor_get(v_specs_1917_, 0);
                v_erased_1924_ = lean_ctor_get(v_specs_1917_, 1);
                v_isSharedCheck_1936_ = (!lean_is_exclusive(v_specs_1917_)) as u8;
                if v_isSharedCheck_1936_ == 0 {
                    v___x_1926_ = v_specs_1917_;
                    v_isShared_1927_ = v_isSharedCheck_1936_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_erased_1924_);
                    lean_inc(v_specs_1923_);
                    lean_dec(v_specs_1917_);
                    v___x_1926_ = lean_box(0);
                    v_isShared_1927_ = v_isSharedCheck_1936_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_pattern_1928_ = lean_ctor_get(v_thm_1916_, 0);
                lean_inc_ref(v_pattern_1928_);
                v___x_1929_ = l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0(v_specs_1923_, v_pattern_1928_, v_thm_1916_);
                if v_isShared_1927_ == 0 {
                    lean_ctor_set(v___x_1926_, 0, v___x_1929_);
                    v___x_1931_ = v___x_1926_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1929_);
                    lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_erased_1924_);
                    v___x_1931_ = v_reuseFailAlloc_1935_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1922_ == 0 {
                    lean_ctor_set(v___x_1921_, 0, v___x_1931_);
                    v___x_1933_ = v___x_1921_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1931_);
                    lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_jps_1918_);
                    lean_ctor_set(v_reuseFailAlloc_1934_, 2, v_nextDeclIdx_1919_);
                    v___x_1933_ = v_reuseFailAlloc_1934_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1933_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1938_: *mut LeanObject,
    mut v_x_1939_: *mut LeanObject,
    mut v_x_1940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    v___x_1941_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1___redArg(v_x_1939_, v_x_1940_);
    return v___x_1941_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1942_: *mut LeanObject,
    mut v_x_1943_: *mut LeanObject,
    mut v_x_1944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1945_: *mut LeanObject = core::ptr::null_mut();
    v_res_1945_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1(v_00_u03b2_1942_, v_x_1943_, v_x_1944_);
    lean_dec(v_x_1944_);
    lean_dec_ref(v_x_1943_);
    return v_res_1945_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1946_: *mut LeanObject,
    mut v_x_1947_: *mut LeanObject,
    mut v_x_1948_: *mut LeanObject,
    mut v_x_1949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    v___x_1950_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2___redArg(v_x_1947_, v_x_1948_, v_x_1949_);
    return v___x_1950_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1951_: *mut LeanObject,
    mut v_x_1952_: *mut LeanObject,
    mut v_x_1953_: usize,
    mut v_x_1954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    v___x_1955_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1952_, v_x_1953_, v_x_1954_);
    return v___x_1955_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b2_1956_: *mut LeanObject,
    mut v_x_1957_: *mut LeanObject,
    mut v_x_1958_: *mut LeanObject,
    mut v_x_1959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2228__boxed_1960_: usize = 0;
    let mut v_res_1961_: *mut LeanObject = core::ptr::null_mut();
    v_x_2228__boxed_1960_ = lean_unbox_usize(v_x_1958_);
    lean_dec(v_x_1958_);
    v_res_1961_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_1956_, v_x_1957_, v_x_2228__boxed_1960_, v_x_1959_);
    lean_dec(v_x_1959_);
    lean_dec_ref(v_x_1957_);
    return v_res_1961_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_1962_: *mut LeanObject,
    mut v_x_1963_: *mut LeanObject,
    mut v_x_1964_: usize,
    mut v_x_1965_: usize,
    mut v_x_1966_: *mut LeanObject,
    mut v_x_1967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    v___x_1968_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg(v_x_1963_, v_x_1964_, v_x_1965_, v_x_1966_, v_x_1967_);
    return v___x_1968_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b2_1969_: *mut LeanObject,
    mut v_x_1970_: *mut LeanObject,
    mut v_x_1971_: *mut LeanObject,
    mut v_x_1972_: *mut LeanObject,
    mut v_x_1973_: *mut LeanObject,
    mut v_x_1974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2239__boxed_1975_: usize = 0;
    let mut v_x_2240__boxed_1976_: usize = 0;
    let mut v_res_1977_: *mut LeanObject = core::ptr::null_mut();
    v_x_2239__boxed_1975_ = lean_unbox_usize(v_x_1971_);
    lean_dec(v_x_1971_);
    v_x_2240__boxed_1976_ = lean_unbox_usize(v_x_1972_);
    lean_dec(v_x_1972_);
    v_res_1977_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_1969_, v_x_1970_, v_x_2239__boxed_1975_, v_x_2240__boxed_1976_, v_x_1973_, v_x_1974_);
    return v_res_1977_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_1978_: *mut LeanObject,
    mut v_keys_1979_: *mut LeanObject,
    mut v_vals_1980_: *mut LeanObject,
    mut v_heq_1981_: *mut LeanObject,
    mut v_i_1982_: *mut LeanObject,
    mut v_k_1983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    v___x_1984_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_keys_1979_, v_vals_1980_, v_i_1982_, v_k_1983_);
    return v___x_1984_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_1985_: *mut LeanObject,
    mut v_keys_1986_: *mut LeanObject,
    mut v_vals_1987_: *mut LeanObject,
    mut v_heq_1988_: *mut LeanObject,
    mut v_i_1989_: *mut LeanObject,
    mut v_k_1990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1991_: *mut LeanObject = core::ptr::null_mut();
    v_res_1991_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b2_1985_, v_keys_1986_, v_vals_1987_, v_heq_1988_, v_i_1989_, v_k_1990_);
    lean_dec(v_k_1990_);
    lean_dec_ref(v_vals_1987_);
    lean_dec_ref(v_keys_1986_);
    return v_res_1991_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__7(
    mut v_00_u03b2_1992_: *mut LeanObject,
    mut v_n_1993_: *mut LeanObject,
    mut v_k_1994_: *mut LeanObject,
    mut v_v_1995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    v___x_1996_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_n_1993_, v_k_1994_, v_v_1995_);
    return v___x_1996_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__8(
    mut v_00_u03b2_1997_: *mut LeanObject,
    mut v_depth_1998_: usize,
    mut v_keys_1999_: *mut LeanObject,
    mut v_vals_2000_: *mut LeanObject,
    mut v_heq_2001_: *mut LeanObject,
    mut v_i_2002_: *mut LeanObject,
    mut v_entries_2003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    v___x_2004_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__8___redArg(v_depth_1998_, v_keys_1999_, v_vals_2000_, v_i_2002_, v_entries_2003_);
    return v___x_2004_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__8___boxed(
    mut v_00_u03b2_2005_: *mut LeanObject,
    mut v_depth_2006_: *mut LeanObject,
    mut v_keys_2007_: *mut LeanObject,
    mut v_vals_2008_: *mut LeanObject,
    mut v_heq_2009_: *mut LeanObject,
    mut v_i_2010_: *mut LeanObject,
    mut v_entries_2011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2012_: usize = 0;
    let mut v_res_2013_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2012_ = lean_unbox_usize(v_depth_2006_);
    lean_dec(v_depth_2006_);
    v_res_2013_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__8(v_00_u03b2_2005_, v_depth_boxed_2012_, v_keys_2007_, v_vals_2008_, v_heq_2009_, v_i_2010_, v_entries_2011_);
    lean_dec_ref(v_vals_2008_);
    lean_dec_ref(v_keys_2007_);
    return v_res_2013_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7_spec__13(
    mut v_x_2014_: *mut LeanObject,
    mut v_keys_2015_: *mut LeanObject,
    mut v_v_2016_: *mut LeanObject,
    mut v_k_2017_: *mut LeanObject,
    mut v_as_2018_: *mut LeanObject,
    mut v_k_2019_: *mut LeanObject,
    mut v_x_2020_: *mut LeanObject,
    mut v_x_2021_: *mut LeanObject,
    mut v_x_2022_: *mut LeanObject,
    mut v_x_2023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    v___x_2024_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7_spec__13___redArg(v_x_2014_, v_keys_2015_, v_v_2016_, v_k_2017_, v_as_2018_, v_k_2019_, v_x_2020_, v_x_2021_);
    return v___x_2024_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7_spec__13___boxed(
    mut v_x_2025_: *mut LeanObject,
    mut v_keys_2026_: *mut LeanObject,
    mut v_v_2027_: *mut LeanObject,
    mut v_k_2028_: *mut LeanObject,
    mut v_as_2029_: *mut LeanObject,
    mut v_k_2030_: *mut LeanObject,
    mut v_x_2031_: *mut LeanObject,
    mut v_x_2032_: *mut LeanObject,
    mut v_x_2033_: *mut LeanObject,
    mut v_x_2034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2035_: *mut LeanObject = core::ptr::null_mut();
    v_res_2035_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7_spec__13(v_x_2025_, v_keys_2026_, v_v_2027_, v_k_2028_, v_as_2029_, v_k_2030_, v_x_2031_, v_x_2032_, v_x_2033_, v_x_2034_);
    lean_dec_ref(v_k_2030_);
    lean_dec_ref(v_keys_2026_);
    lean_dec(v_x_2025_);
    return v_res_2035_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__7_spec__9(
    mut v_00_u03b2_2036_: *mut LeanObject,
    mut v_x_2037_: *mut LeanObject,
    mut v_x_2038_: *mut LeanObject,
    mut v_x_2039_: *mut LeanObject,
    mut v_x_2040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    v___x_2041_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__7_spec__9___redArg(v_x_2037_, v_x_2038_, v_x_2039_, v_x_2040_);
    return v___x_2041_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(
    mut v_x_2042_: *mut LeanObject,
    mut v___y_2043_: *mut LeanObject,
    mut v___y_2044_: *mut LeanObject,
    mut v___y_2045_: *mut LeanObject,
    mut v___y_2046_: *mut LeanObject,
    mut v___y_2047_: *mut LeanObject,
    mut v___y_2048_: *mut LeanObject,
    mut v___y_2049_: *mut LeanObject,
    mut v___y_2050_: *mut LeanObject,
    mut v___y_2051_: *mut LeanObject,
    mut v___y_2052_: *mut LeanObject,
    mut v___y_2053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_2049_);
    lean_inc_ref(v___y_2048_);
    lean_inc(v___y_2047_);
    lean_inc_ref(v___y_2046_);
    lean_inc(v___y_2045_);
    lean_inc(v___y_2044_);
    lean_inc_ref(v___y_2043_);
    v___x_2055_ = lean_apply_12(
        v_x_2042_,
        v___y_2043_,
        v___y_2044_,
        v___y_2045_,
        v___y_2046_,
        v___y_2047_,
        v___y_2048_,
        v___y_2049_,
        v___y_2050_,
        v___y_2051_,
        v___y_2052_,
        v___y_2053_,
        lean_box(0),
    );
    return v___x_2055_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0___boxed(
    mut v_x_2056_: *mut LeanObject,
    mut v___y_2057_: *mut LeanObject,
    mut v___y_2058_: *mut LeanObject,
    mut v___y_2059_: *mut LeanObject,
    mut v___y_2060_: *mut LeanObject,
    mut v___y_2061_: *mut LeanObject,
    mut v___y_2062_: *mut LeanObject,
    mut v___y_2063_: *mut LeanObject,
    mut v___y_2064_: *mut LeanObject,
    mut v___y_2065_: *mut LeanObject,
    mut v___y_2066_: *mut LeanObject,
    mut v___y_2067_: *mut LeanObject,
    mut v___y_2068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2069_: *mut LeanObject = core::ptr::null_mut();
    v_res_2069_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(v_x_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
    lean_dec(v___y_2063_);
    lean_dec_ref(v___y_2062_);
    lean_dec(v___y_2061_);
    lean_dec_ref(v___y_2060_);
    lean_dec(v___y_2059_);
    lean_dec(v___y_2058_);
    lean_dec_ref(v___y_2057_);
    return v_res_2069_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(
    mut v_mvarId_2070_: *mut LeanObject,
    mut v_x_2071_: *mut LeanObject,
    mut v___y_2072_: *mut LeanObject,
    mut v___y_2073_: *mut LeanObject,
    mut v___y_2074_: *mut LeanObject,
    mut v___y_2075_: *mut LeanObject,
    mut v___y_2076_: *mut LeanObject,
    mut v___y_2077_: *mut LeanObject,
    mut v___y_2078_: *mut LeanObject,
    mut v___y_2079_: *mut LeanObject,
    mut v___y_2080_: *mut LeanObject,
    mut v___y_2081_: *mut LeanObject,
    mut v___y_2082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2089_: u8 = 0;
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2093_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_2078_);
                lean_inc_ref(v___y_2077_);
                lean_inc(v___y_2076_);
                lean_inc_ref(v___y_2075_);
                lean_inc(v___y_2074_);
                lean_inc(v___y_2073_);
                lean_inc_ref(v___y_2072_);
                v___f_2084_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 8);
                lean_closure_set(v___f_2084_, 0, v_x_2071_);
                lean_closure_set(v___f_2084_, 1, v___y_2072_);
                lean_closure_set(v___f_2084_, 2, v___y_2073_);
                lean_closure_set(v___f_2084_, 3, v___y_2074_);
                lean_closure_set(v___f_2084_, 4, v___y_2075_);
                lean_closure_set(v___f_2084_, 5, v___y_2076_);
                lean_closure_set(v___f_2084_, 6, v___y_2077_);
                lean_closure_set(v___f_2084_, 7, v___y_2078_);
                v___x_2085_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_2070_,
                    v___f_2084_,
                    v___y_2079_,
                    v___y_2080_,
                    v___y_2081_,
                    v___y_2082_,
                );
                if lean_obj_tag(v___x_2085_) == 0 {
                    return v___x_2085_;
                } else {
                    v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
                    v_isSharedCheck_2093_ = (!lean_is_exclusive(v___x_2085_)) as u8;
                    if v_isSharedCheck_2093_ == 0 {
                        v___x_2088_ = v___x_2085_;
                        v_isShared_2089_ = v_isSharedCheck_2093_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2086_);
                        lean_dec(v___x_2085_);
                        v___x_2088_ = lean_box(0);
                        v_isShared_2089_ = v_isSharedCheck_2093_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2089_ == 0 {
                    v___x_2091_ = v___x_2088_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
                    v___x_2091_ = v_reuseFailAlloc_2092_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2091_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___boxed(
    mut v_mvarId_2094_: *mut LeanObject,
    mut v_x_2095_: *mut LeanObject,
    mut v___y_2096_: *mut LeanObject,
    mut v___y_2097_: *mut LeanObject,
    mut v___y_2098_: *mut LeanObject,
    mut v___y_2099_: *mut LeanObject,
    mut v___y_2100_: *mut LeanObject,
    mut v___y_2101_: *mut LeanObject,
    mut v___y_2102_: *mut LeanObject,
    mut v___y_2103_: *mut LeanObject,
    mut v___y_2104_: *mut LeanObject,
    mut v___y_2105_: *mut LeanObject,
    mut v___y_2106_: *mut LeanObject,
    mut v___y_2107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2108_: *mut LeanObject = core::ptr::null_mut();
    v_res_2108_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_mvarId_2094_, v_x_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
    lean_dec(v___y_2106_);
    lean_dec_ref(v___y_2105_);
    lean_dec(v___y_2104_);
    lean_dec_ref(v___y_2103_);
    lean_dec(v___y_2102_);
    lean_dec_ref(v___y_2101_);
    lean_dec(v___y_2100_);
    lean_dec_ref(v___y_2099_);
    lean_dec(v___y_2098_);
    lean_dec(v___y_2097_);
    lean_dec_ref(v___y_2096_);
    return v_res_2108_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1(
    mut v_00_u03b1_2109_: *mut LeanObject,
    mut v_mvarId_2110_: *mut LeanObject,
    mut v_x_2111_: *mut LeanObject,
    mut v___y_2112_: *mut LeanObject,
    mut v___y_2113_: *mut LeanObject,
    mut v___y_2114_: *mut LeanObject,
    mut v___y_2115_: *mut LeanObject,
    mut v___y_2116_: *mut LeanObject,
    mut v___y_2117_: *mut LeanObject,
    mut v___y_2118_: *mut LeanObject,
    mut v___y_2119_: *mut LeanObject,
    mut v___y_2120_: *mut LeanObject,
    mut v___y_2121_: *mut LeanObject,
    mut v___y_2122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    v___x_2124_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_mvarId_2110_, v_x_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
    return v___x_2124_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___boxed(
    mut v_00_u03b1_2125_: *mut LeanObject,
    mut v_mvarId_2126_: *mut LeanObject,
    mut v_x_2127_: *mut LeanObject,
    mut v___y_2128_: *mut LeanObject,
    mut v___y_2129_: *mut LeanObject,
    mut v___y_2130_: *mut LeanObject,
    mut v___y_2131_: *mut LeanObject,
    mut v___y_2132_: *mut LeanObject,
    mut v___y_2133_: *mut LeanObject,
    mut v___y_2134_: *mut LeanObject,
    mut v___y_2135_: *mut LeanObject,
    mut v___y_2136_: *mut LeanObject,
    mut v___y_2137_: *mut LeanObject,
    mut v___y_2138_: *mut LeanObject,
    mut v___y_2139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2140_: *mut LeanObject = core::ptr::null_mut();
    v_res_2140_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1(v_00_u03b1_2125_, v_mvarId_2126_, v_x_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
    lean_dec(v___y_2138_);
    lean_dec_ref(v___y_2137_);
    lean_dec(v___y_2136_);
    lean_dec_ref(v___y_2135_);
    lean_dec(v___y_2134_);
    lean_dec_ref(v___y_2133_);
    lean_dec(v___y_2132_);
    lean_dec_ref(v___y_2131_);
    lean_dec(v___y_2130_);
    lean_dec(v___y_2129_);
    lean_dec_ref(v___y_2128_);
    return v_res_2140_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(
    mut v_as_2141_: *mut LeanObject,
    mut v_i_2142_: usize,
    mut v_stop_2143_: usize,
    mut v_b_2144_: *mut LeanObject,
    mut v___y_2145_: *mut LeanObject,
    mut v___y_2146_: *mut LeanObject,
    mut v___y_2147_: *mut LeanObject,
    mut v___y_2148_: *mut LeanObject,
    mut v___y_2149_: *mut LeanObject,
    mut v___y_2150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: usize = 0;
    let mut v___x_2155_: usize = 0;
    let mut v___x_2157_: u8 = 0;
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2162_: u8 = 0;
    let mut v___x_2163_: u8 = 0;
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2175_: u8 = 0;
    let mut v___y_2177_: u8 = 0;
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: u8 = 0;
    let mut v___x_2182_: u8 = 0;
    let mut v_isSharedCheck_2183_: u8 = 0;
    let mut v_reuseFailAlloc_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2185_: u8 = 0;
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2157_ = lean_usize_dec_eq(v_i_2142_, v_stop_2143_);
                if v___x_2157_ == 0 {
                    v___x_2158_ = lean_array_uget(v_as_2141_, v_i_2142_);
                    if lean_obj_tag(v___x_2158_) == 0 {
                        v_a_2153_ = v_b_2144_;
                        state = 1;
                        continue;
                    } else {
                        v_val_2159_ = lean_ctor_get(v___x_2158_, 0);
                        v_isSharedCheck_2185_ = (!lean_is_exclusive(v___x_2158_)) as u8;
                        if v_isSharedCheck_2185_ == 0 {
                            v___x_2161_ = v___x_2158_;
                            v_isShared_2162_ = v_isSharedCheck_2185_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_2159_);
                            lean_dec(v___x_2158_);
                            v___x_2161_ = lean_box(0);
                            v_isShared_2162_ = v_isSharedCheck_2185_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_2186_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2186_, 0, v_b_2144_);
                    return v___x_2186_;
                }
            }
            1 => {
                v___x_2154_ = 1usize;
                v___x_2155_ = lean_usize_add(v_i_2142_, v___x_2154_);
                v_i_2142_ = v___x_2155_;
                v_b_2144_ = v_a_2153_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2163_ = l_Lean_LocalDecl_isAuxDecl(v_val_2159_);
                if v___x_2163_ == 0 {
                    v___x_2164_ = l_Lean_LocalDecl_fvarId(v_val_2159_);
                    lean_dec(v_val_2159_);
                    if v_isShared_2162_ == 0 {
                        lean_ctor_set(v___x_2161_, 0, v___x_2164_);
                        v___x_2166_ = v___x_2161_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2164_);
                        v___x_2166_ = v_reuseFailAlloc_2184_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2161_);
                    lean_dec(v_val_2159_);
                    v_a_2153_ = v_b_2144_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2167_ = lean_unsigned_to_nat(100);
                v___x_2168_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew(
                    v___x_2166_,
                    v___x_2167_,
                    v___y_2145_,
                    v___y_2146_,
                    v___y_2147_,
                    v___y_2148_,
                    v___y_2149_,
                    v___y_2150_,
                );
                if lean_obj_tag(v___x_2168_) == 0 {
                    v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
                    lean_inc(v_a_2169_);
                    lean_dec_ref_known(v___x_2168_, 1);
                    if lean_obj_tag(v_a_2169_) == 1 {
                        v_val_2170_ = lean_ctor_get(v_a_2169_, 0);
                        lean_inc(v_val_2170_);
                        lean_dec_ref_known(v_a_2169_, 1);
                        v___x_2171_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec(
                            v_b_2144_,
                            v_val_2170_,
                        );
                        v_a_2153_ = v___x_2171_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_a_2169_);
                        v_a_2153_ = v_b_2144_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2172_ = lean_ctor_get(v___x_2168_, 0);
                    v_isSharedCheck_2183_ = (!lean_is_exclusive(v___x_2168_)) as u8;
                    if v_isSharedCheck_2183_ == 0 {
                        v___x_2174_ = v___x_2168_;
                        v_isShared_2175_ = v_isSharedCheck_2183_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2172_);
                        lean_dec(v___x_2168_);
                        v___x_2174_ = lean_box(0);
                        v_isShared_2175_ = v_isSharedCheck_2183_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2181_ = l_Lean_Exception_isInterrupt(v_a_2172_);
                if v___x_2181_ == 0 {
                    lean_inc(v_a_2172_);
                    v___x_2182_ = l_Lean_Exception_isRuntime(v_a_2172_);
                    v___y_2177_ = v___x_2182_;
                    state = 5;
                    continue;
                } else {
                    v___y_2177_ = v___x_2181_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v___y_2177_ == 0 {
                    lean_del_object(v___x_2174_);
                    lean_dec(v_a_2172_);
                    v_a_2153_ = v_b_2144_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_b_2144_);
                    if v_isShared_2175_ == 0 {
                        v___x_2179_ = v___x_2174_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2172_);
                        v___x_2179_ = v_reuseFailAlloc_2180_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_2179_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_as_2187_: *mut LeanObject,
    mut v_i_2188_: *mut LeanObject,
    mut v_stop_2189_: *mut LeanObject,
    mut v_b_2190_: *mut LeanObject,
    mut v___y_2191_: *mut LeanObject,
    mut v___y_2192_: *mut LeanObject,
    mut v___y_2193_: *mut LeanObject,
    mut v___y_2194_: *mut LeanObject,
    mut v___y_2195_: *mut LeanObject,
    mut v___y_2196_: *mut LeanObject,
    mut v___y_2197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2198_: usize = 0;
    let mut v_stop_boxed_2199_: usize = 0;
    let mut v_res_2200_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2198_ = lean_unbox_usize(v_i_2188_);
    lean_dec(v_i_2188_);
    v_stop_boxed_2199_ = lean_unbox_usize(v_stop_2189_);
    lean_dec(v_stop_2189_);
    v_res_2200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_as_2187_, v_i_boxed_2198_, v_stop_boxed_2199_, v_b_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
    lean_dec(v___y_2196_);
    lean_dec_ref(v___y_2195_);
    lean_dec(v___y_2194_);
    lean_dec_ref(v___y_2193_);
    lean_dec(v___y_2192_);
    lean_dec_ref(v___y_2191_);
    lean_dec_ref(v_as_2187_);
    return v_res_2200_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(
    mut v_x_2201_: *mut LeanObject,
    mut v_x_2202_: *mut LeanObject,
    mut v___y_2203_: *mut LeanObject,
    mut v___y_2204_: *mut LeanObject,
    mut v___y_2205_: *mut LeanObject,
    mut v___y_2206_: *mut LeanObject,
    mut v___y_2207_: *mut LeanObject,
    mut v___y_2208_: *mut LeanObject,
    mut v___y_2209_: *mut LeanObject,
    mut v___y_2210_: *mut LeanObject,
    mut v___y_2211_: *mut LeanObject,
    mut v___y_2212_: *mut LeanObject,
    mut v___y_2213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2218_: u8 = 0;
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: u8 = 0;
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: usize = 0;
    let mut v___x_2230_: usize = 0;
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: usize = 0;
    let mut v___x_2233_: usize = 0;
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2235_: u8 = 0;
    let mut v_vs_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2239_: u8 = 0;
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: u8 = 0;
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: u8 = 0;
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: usize = 0;
    let mut v___x_2251_: usize = 0;
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: usize = 0;
    let mut v___x_2254_: usize = 0;
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2256_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2201_) == 0 {
                    v_cs_2215_ = lean_ctor_get(v_x_2201_, 0);
                    v_isSharedCheck_2235_ = (!lean_is_exclusive(v_x_2201_)) as u8;
                    if v_isSharedCheck_2235_ == 0 {
                        v___x_2217_ = v_x_2201_;
                        v_isShared_2218_ = v_isSharedCheck_2235_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_cs_2215_);
                        lean_dec(v_x_2201_);
                        v___x_2217_ = lean_box(0);
                        v_isShared_2218_ = v_isSharedCheck_2235_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_2236_ = lean_ctor_get(v_x_2201_, 0);
                    v_isSharedCheck_2256_ = (!lean_is_exclusive(v_x_2201_)) as u8;
                    if v_isSharedCheck_2256_ == 0 {
                        v___x_2238_ = v_x_2201_;
                        v_isShared_2239_ = v_isSharedCheck_2256_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_vs_2236_);
                        lean_dec(v_x_2201_);
                        v___x_2238_ = lean_box(0);
                        v_isShared_2239_ = v_isSharedCheck_2256_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2219_ = lean_unsigned_to_nat(0);
                v___x_2220_ = lean_array_get_size(v_cs_2215_);
                v___x_2221_ = lean_nat_dec_lt(v___x_2219_, v___x_2220_);
                if v___x_2221_ == 0 {
                    lean_dec_ref(v_cs_2215_);
                    if v_isShared_2218_ == 0 {
                        lean_ctor_set(v___x_2217_, 0, v_x_2202_);
                        v___x_2223_ = v___x_2217_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_x_2202_);
                        v___x_2223_ = v_reuseFailAlloc_2224_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2225_ = lean_nat_dec_le(v___x_2220_, v___x_2220_);
                    if v___x_2225_ == 0 {
                        if v___x_2221_ == 0 {
                            lean_dec_ref(v_cs_2215_);
                            if v_isShared_2218_ == 0 {
                                lean_ctor_set(v___x_2217_, 0, v_x_2202_);
                                v___x_2227_ = v___x_2217_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_x_2202_);
                                v___x_2227_ = v_reuseFailAlloc_2228_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2217_);
                            v___x_2229_ = 0usize;
                            v___x_2230_ = lean_usize_of_nat(v___x_2220_);
                            v___x_2231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_2215_, v___x_2229_, v___x_2230_, v_x_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
                            lean_dec_ref(v_cs_2215_);
                            return v___x_2231_;
                        }
                    } else {
                        lean_del_object(v___x_2217_);
                        v___x_2232_ = 0usize;
                        v___x_2233_ = lean_usize_of_nat(v___x_2220_);
                        v___x_2234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_2215_, v___x_2232_, v___x_2233_, v_x_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
                        lean_dec_ref(v_cs_2215_);
                        return v___x_2234_;
                    }
                }
            }
            2 => {
                return v___x_2223_;
            }
            3 => {
                return v___x_2227_;
            }
            4 => {
                v___x_2240_ = lean_unsigned_to_nat(0);
                v___x_2241_ = lean_array_get_size(v_vs_2236_);
                v___x_2242_ = lean_nat_dec_lt(v___x_2240_, v___x_2241_);
                if v___x_2242_ == 0 {
                    lean_dec_ref(v_vs_2236_);
                    if v_isShared_2239_ == 0 {
                        lean_ctor_set_tag(v___x_2238_, 0);
                        lean_ctor_set(v___x_2238_, 0, v_x_2202_);
                        v___x_2244_ = v___x_2238_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_x_2202_);
                        v___x_2244_ = v_reuseFailAlloc_2245_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_2246_ = lean_nat_dec_le(v___x_2241_, v___x_2241_);
                    if v___x_2246_ == 0 {
                        if v___x_2242_ == 0 {
                            lean_dec_ref(v_vs_2236_);
                            if v_isShared_2239_ == 0 {
                                lean_ctor_set_tag(v___x_2238_, 0);
                                lean_ctor_set(v___x_2238_, 0, v_x_2202_);
                                v___x_2248_ = v___x_2238_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_x_2202_);
                                v___x_2248_ = v_reuseFailAlloc_2249_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2238_);
                            v___x_2250_ = 0usize;
                            v___x_2251_ = lean_usize_of_nat(v___x_2241_);
                            v___x_2252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_2236_, v___x_2250_, v___x_2251_, v_x_2202_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
                            lean_dec_ref(v_vs_2236_);
                            return v___x_2252_;
                        }
                    } else {
                        lean_del_object(v___x_2238_);
                        v___x_2253_ = 0usize;
                        v___x_2254_ = lean_usize_of_nat(v___x_2241_);
                        v___x_2255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_2236_, v___x_2253_, v___x_2254_, v_x_2202_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
                        lean_dec_ref(v_vs_2236_);
                        return v___x_2255_;
                    }
                }
            }
            5 => {
                return v___x_2244_;
            }
            6 => {
                return v___x_2248_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(
    mut v_as_2257_: *mut LeanObject,
    mut v_i_2258_: usize,
    mut v_stop_2259_: usize,
    mut v_b_2260_: *mut LeanObject,
    mut v___y_2261_: *mut LeanObject,
    mut v___y_2262_: *mut LeanObject,
    mut v___y_2263_: *mut LeanObject,
    mut v___y_2264_: *mut LeanObject,
    mut v___y_2265_: *mut LeanObject,
    mut v___y_2266_: *mut LeanObject,
    mut v___y_2267_: *mut LeanObject,
    mut v___y_2268_: *mut LeanObject,
    mut v___y_2269_: *mut LeanObject,
    mut v___y_2270_: *mut LeanObject,
    mut v___y_2271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2273_: u8 = 0;
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: usize = 0;
    let mut v___x_2278_: usize = 0;
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2273_ = lean_usize_dec_eq(v_i_2258_, v_stop_2259_);
                if v___x_2273_ == 0 {
                    v___x_2274_ = lean_array_uget_borrowed(v_as_2257_, v_i_2258_);
                    lean_inc(v___x_2274_);
                    v___x_2275_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v___x_2274_, v_b_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
                    if lean_obj_tag(v___x_2275_) == 0 {
                        v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
                        lean_inc(v_a_2276_);
                        lean_dec_ref_known(v___x_2275_, 1);
                        v___x_2277_ = 1usize;
                        v___x_2278_ = lean_usize_add(v_i_2258_, v___x_2277_);
                        v_i_2258_ = v___x_2278_;
                        v_b_2260_ = v_a_2276_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2275_;
                    }
                } else {
                    v___x_2280_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2280_, 0, v_b_2260_);
                    return v___x_2280_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_as_2281_: *mut LeanObject,
    mut v_i_2282_: *mut LeanObject,
    mut v_stop_2283_: *mut LeanObject,
    mut v_b_2284_: *mut LeanObject,
    mut v___y_2285_: *mut LeanObject,
    mut v___y_2286_: *mut LeanObject,
    mut v___y_2287_: *mut LeanObject,
    mut v___y_2288_: *mut LeanObject,
    mut v___y_2289_: *mut LeanObject,
    mut v___y_2290_: *mut LeanObject,
    mut v___y_2291_: *mut LeanObject,
    mut v___y_2292_: *mut LeanObject,
    mut v___y_2293_: *mut LeanObject,
    mut v___y_2294_: *mut LeanObject,
    mut v___y_2295_: *mut LeanObject,
    mut v___y_2296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2297_: usize = 0;
    let mut v_stop_boxed_2298_: usize = 0;
    let mut v_res_2299_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2297_ = lean_unbox_usize(v_i_2282_);
    lean_dec(v_i_2282_);
    v_stop_boxed_2298_ = lean_unbox_usize(v_stop_2283_);
    lean_dec(v_stop_2283_);
    v_res_2299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_as_2281_, v_i_boxed_2297_, v_stop_boxed_2298_, v_b_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
    lean_dec(v___y_2295_);
    lean_dec_ref(v___y_2294_);
    lean_dec(v___y_2293_);
    lean_dec_ref(v___y_2292_);
    lean_dec(v___y_2291_);
    lean_dec_ref(v___y_2290_);
    lean_dec(v___y_2289_);
    lean_dec_ref(v___y_2288_);
    lean_dec(v___y_2287_);
    lean_dec(v___y_2286_);
    lean_dec_ref(v___y_2285_);
    lean_dec_ref(v_as_2281_);
    return v_res_2299_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4___boxed(
    mut v_x_2300_: *mut LeanObject,
    mut v_x_2301_: *mut LeanObject,
    mut v___y_2302_: *mut LeanObject,
    mut v___y_2303_: *mut LeanObject,
    mut v___y_2304_: *mut LeanObject,
    mut v___y_2305_: *mut LeanObject,
    mut v___y_2306_: *mut LeanObject,
    mut v___y_2307_: *mut LeanObject,
    mut v___y_2308_: *mut LeanObject,
    mut v___y_2309_: *mut LeanObject,
    mut v___y_2310_: *mut LeanObject,
    mut v___y_2311_: *mut LeanObject,
    mut v___y_2312_: *mut LeanObject,
    mut v___y_2313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2314_: *mut LeanObject = core::ptr::null_mut();
    v_res_2314_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v_x_2300_, v_x_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
    lean_dec(v___y_2312_);
    lean_dec_ref(v___y_2311_);
    lean_dec(v___y_2310_);
    lean_dec_ref(v___y_2309_);
    lean_dec(v___y_2308_);
    lean_dec_ref(v___y_2307_);
    lean_dec(v___y_2306_);
    lean_dec_ref(v___y_2305_);
    lean_dec(v___y_2304_);
    lean_dec(v___y_2303_);
    lean_dec_ref(v___y_2302_);
    return v_res_2314_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0()
-> *mut LeanObject {
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    v___x_2315_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
    return v___x_2315_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(
    mut v_x_2316_: *mut LeanObject,
    mut v_x_2317_: usize,
    mut v_x_2318_: usize,
    mut v_x_2319_: *mut LeanObject,
    mut v___y_2320_: *mut LeanObject,
    mut v___y_2321_: *mut LeanObject,
    mut v___y_2322_: *mut LeanObject,
    mut v___y_2323_: *mut LeanObject,
    mut v___y_2324_: *mut LeanObject,
    mut v___y_2325_: *mut LeanObject,
    mut v___y_2326_: *mut LeanObject,
    mut v___y_2327_: *mut LeanObject,
    mut v___y_2328_: *mut LeanObject,
    mut v___y_2329_: *mut LeanObject,
    mut v___y_2330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: usize = 0;
    let mut v_j_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: usize = 0;
    let mut v___x_2338_: usize = 0;
    let mut v___x_2339_: usize = 0;
    let mut v___x_2340_: usize = 0;
    let mut v___x_2341_: usize = 0;
    let mut v___x_2342_: usize = 0;
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: u8 = 0;
    let mut v___x_2349_: u8 = 0;
    let mut v___x_2350_: usize = 0;
    let mut v___x_2351_: usize = 0;
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: usize = 0;
    let mut v___x_2354_: usize = 0;
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2359_: u8 = 0;
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: u8 = 0;
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: u8 = 0;
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: usize = 0;
    let mut v___x_2371_: usize = 0;
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: usize = 0;
    let mut v___x_2374_: usize = 0;
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2376_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2316_) == 0 {
                    v_cs_2332_ = lean_ctor_get(v_x_2316_, 0);
                    lean_inc_ref(v_cs_2332_);
                    lean_dec_ref_known(v_x_2316_, 1);
                    v___x_2333_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0);
                    v___x_2334_ = lean_usize_shift_right(v_x_2317_, v_x_2318_);
                    v_j_2335_ = lean_usize_to_nat(v___x_2334_);
                    v___x_2336_ = lean_array_get_borrowed(v___x_2333_, v_cs_2332_, v_j_2335_);
                    v___x_2337_ = 1usize;
                    v___x_2338_ = lean_usize_shift_left(v___x_2337_, v_x_2318_);
                    v___x_2339_ = lean_usize_sub(v___x_2338_, v___x_2337_);
                    v___x_2340_ = lean_usize_land(v_x_2317_, v___x_2339_);
                    v___x_2341_ = 5usize;
                    v___x_2342_ = lean_usize_sub(v_x_2318_, v___x_2341_);
                    lean_inc(v___x_2336_);
                    v___x_2343_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v___x_2336_, v___x_2340_, v___x_2342_, v_x_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
                    if lean_obj_tag(v___x_2343_) == 0 {
                        v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
                        lean_inc(v_a_2344_);
                        v___x_2345_ = lean_unsigned_to_nat(1);
                        v___x_2346_ = lean_nat_add(v_j_2335_, v___x_2345_);
                        lean_dec(v_j_2335_);
                        v___x_2347_ = lean_array_get_size(v_cs_2332_);
                        v___x_2348_ = lean_nat_dec_lt(v___x_2346_, v___x_2347_);
                        if v___x_2348_ == 0 {
                            lean_dec(v___x_2346_);
                            lean_dec(v_a_2344_);
                            lean_dec_ref(v_cs_2332_);
                            return v___x_2343_;
                        } else {
                            v___x_2349_ = lean_nat_dec_le(v___x_2347_, v___x_2347_);
                            if v___x_2349_ == 0 {
                                if v___x_2348_ == 0 {
                                    lean_dec(v___x_2346_);
                                    lean_dec(v_a_2344_);
                                    lean_dec_ref(v_cs_2332_);
                                    return v___x_2343_;
                                } else {
                                    lean_dec_ref_known(v___x_2343_, 1);
                                    v___x_2350_ = lean_usize_of_nat(v___x_2346_);
                                    lean_dec(v___x_2346_);
                                    v___x_2351_ = lean_usize_of_nat(v___x_2347_);
                                    v___x_2352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_2332_, v___x_2350_, v___x_2351_, v_a_2344_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
                                    lean_dec_ref(v_cs_2332_);
                                    return v___x_2352_;
                                }
                            } else {
                                lean_dec_ref_known(v___x_2343_, 1);
                                v___x_2353_ = lean_usize_of_nat(v___x_2346_);
                                lean_dec(v___x_2346_);
                                v___x_2354_ = lean_usize_of_nat(v___x_2347_);
                                v___x_2355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_2332_, v___x_2353_, v___x_2354_, v_a_2344_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
                                lean_dec_ref(v_cs_2332_);
                                return v___x_2355_;
                            }
                        }
                    } else {
                        lean_dec(v_j_2335_);
                        lean_dec_ref(v_cs_2332_);
                        return v___x_2343_;
                    }
                } else {
                    v_vs_2356_ = lean_ctor_get(v_x_2316_, 0);
                    v_isSharedCheck_2376_ = (!lean_is_exclusive(v_x_2316_)) as u8;
                    if v_isSharedCheck_2376_ == 0 {
                        v___x_2358_ = v_x_2316_;
                        v_isShared_2359_ = v_isSharedCheck_2376_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_vs_2356_);
                        lean_dec(v_x_2316_);
                        v___x_2358_ = lean_box(0);
                        v_isShared_2359_ = v_isSharedCheck_2376_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2360_ = lean_usize_to_nat(v_x_2317_);
                v___x_2361_ = lean_array_get_size(v_vs_2356_);
                v___x_2362_ = lean_nat_dec_lt(v___x_2360_, v___x_2361_);
                if v___x_2362_ == 0 {
                    lean_dec(v___x_2360_);
                    lean_dec_ref(v_vs_2356_);
                    if v_isShared_2359_ == 0 {
                        lean_ctor_set_tag(v___x_2358_, 0);
                        lean_ctor_set(v___x_2358_, 0, v_x_2319_);
                        v___x_2364_ = v___x_2358_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_x_2319_);
                        v___x_2364_ = v_reuseFailAlloc_2365_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2366_ = lean_nat_dec_le(v___x_2361_, v___x_2361_);
                    if v___x_2366_ == 0 {
                        if v___x_2362_ == 0 {
                            lean_dec(v___x_2360_);
                            lean_dec_ref(v_vs_2356_);
                            if v_isShared_2359_ == 0 {
                                lean_ctor_set_tag(v___x_2358_, 0);
                                lean_ctor_set(v___x_2358_, 0, v_x_2319_);
                                v___x_2368_ = v___x_2358_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_x_2319_);
                                v___x_2368_ = v_reuseFailAlloc_2369_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2358_);
                            v___x_2370_ = lean_usize_of_nat(v___x_2360_);
                            lean_dec(v___x_2360_);
                            v___x_2371_ = lean_usize_of_nat(v___x_2361_);
                            v___x_2372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_2356_, v___x_2370_, v___x_2371_, v_x_2319_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
                            lean_dec_ref(v_vs_2356_);
                            return v___x_2372_;
                        }
                    } else {
                        lean_del_object(v___x_2358_);
                        v___x_2373_ = lean_usize_of_nat(v___x_2360_);
                        lean_dec(v___x_2360_);
                        v___x_2374_ = lean_usize_of_nat(v___x_2361_);
                        v___x_2375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_2356_, v___x_2373_, v___x_2374_, v_x_2319_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
                        lean_dec_ref(v_vs_2356_);
                        return v___x_2375_;
                    }
                }
            }
            2 => {
                return v___x_2364_;
            }
            3 => {
                return v___x_2368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___boxed(
    mut v_x_2377_: *mut LeanObject,
    mut v_x_2378_: *mut LeanObject,
    mut v_x_2379_: *mut LeanObject,
    mut v_x_2380_: *mut LeanObject,
    mut v___y_2381_: *mut LeanObject,
    mut v___y_2382_: *mut LeanObject,
    mut v___y_2383_: *mut LeanObject,
    mut v___y_2384_: *mut LeanObject,
    mut v___y_2385_: *mut LeanObject,
    mut v___y_2386_: *mut LeanObject,
    mut v___y_2387_: *mut LeanObject,
    mut v___y_2388_: *mut LeanObject,
    mut v___y_2389_: *mut LeanObject,
    mut v___y_2390_: *mut LeanObject,
    mut v___y_2391_: *mut LeanObject,
    mut v___y_2392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_24362__boxed_2393_: usize = 0;
    let mut v_x_24363__boxed_2394_: usize = 0;
    let mut v_res_2395_: *mut LeanObject = core::ptr::null_mut();
    v_x_24362__boxed_2393_ = lean_unbox_usize(v_x_2378_);
    lean_dec(v_x_2378_);
    v_x_24363__boxed_2394_ = lean_unbox_usize(v_x_2379_);
    lean_dec(v_x_2379_);
    v_res_2395_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v_x_2377_, v_x_24362__boxed_2393_, v_x_24363__boxed_2394_, v_x_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
    lean_dec(v___y_2391_);
    lean_dec_ref(v___y_2390_);
    lean_dec(v___y_2389_);
    lean_dec_ref(v___y_2388_);
    lean_dec(v___y_2387_);
    lean_dec_ref(v___y_2386_);
    lean_dec(v___y_2385_);
    lean_dec_ref(v___y_2384_);
    lean_dec(v___y_2383_);
    lean_dec(v___y_2382_);
    lean_dec_ref(v___y_2381_);
    return v_res_2395_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(
    mut v_t_2396_: *mut LeanObject,
    mut v_init_2397_: *mut LeanObject,
    mut v_start_2398_: *mut LeanObject,
    mut v___y_2399_: *mut LeanObject,
    mut v___y_2400_: *mut LeanObject,
    mut v___y_2401_: *mut LeanObject,
    mut v___y_2402_: *mut LeanObject,
    mut v___y_2403_: *mut LeanObject,
    mut v___y_2404_: *mut LeanObject,
    mut v___y_2405_: *mut LeanObject,
    mut v___y_2406_: *mut LeanObject,
    mut v___y_2407_: *mut LeanObject,
    mut v___y_2408_: *mut LeanObject,
    mut v___y_2409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: u8 = 0;
    v___x_2411_ = lean_unsigned_to_nat(0);
    v___x_2412_ = lean_nat_dec_eq(v_start_2398_, v___x_2411_);
    if v___x_2412_ == 0 {
        let mut v_root_2413_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_2414_: *mut LeanObject = core::ptr::null_mut();
        let mut v_shift_2415_: usize = 0;
        let mut v_tailOff_2416_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2417_: u8 = 0;
        v_root_2413_ = lean_ctor_get(v_t_2396_, 0);
        lean_inc_ref(v_root_2413_);
        v_tail_2414_ = lean_ctor_get(v_t_2396_, 1);
        lean_inc_ref(v_tail_2414_);
        v_shift_2415_ = lean_ctor_get_usize(v_t_2396_, 4);
        v_tailOff_2416_ = lean_ctor_get(v_t_2396_, 3);
        lean_inc(v_tailOff_2416_);
        lean_dec_ref(v_t_2396_);
        v___x_2417_ = lean_nat_dec_le(v_tailOff_2416_, v_start_2398_);
        if v___x_2417_ == 0 {
            let mut v___x_2418_: usize = 0;
            let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_tailOff_2416_);
            v___x_2418_ = lean_usize_of_nat(v_start_2398_);
            v___x_2419_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v_root_2413_, v___x_2418_, v_shift_2415_, v_init_2397_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
            if lean_obj_tag(v___x_2419_) == 0 {
                let mut v_a_2420_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2422_: u8 = 0;
                v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
                lean_inc(v_a_2420_);
                v___x_2421_ = lean_array_get_size(v_tail_2414_);
                v___x_2422_ = lean_nat_dec_lt(v___x_2411_, v___x_2421_);
                if v___x_2422_ == 0 {
                    lean_dec(v_a_2420_);
                    lean_dec_ref(v_tail_2414_);
                    return v___x_2419_;
                } else {
                    let mut v___x_2423_: u8 = 0;
                    v___x_2423_ = lean_nat_dec_le(v___x_2421_, v___x_2421_);
                    if v___x_2423_ == 0 {
                        if v___x_2422_ == 0 {
                            lean_dec(v_a_2420_);
                            lean_dec_ref(v_tail_2414_);
                            return v___x_2419_;
                        } else {
                            let mut v___x_2424_: usize = 0;
                            let mut v___x_2425_: usize = 0;
                            let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec_ref_known(v___x_2419_, 1);
                            v___x_2424_ = 0usize;
                            v___x_2425_ = lean_usize_of_nat(v___x_2421_);
                            v___x_2426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_2414_, v___x_2424_, v___x_2425_, v_a_2420_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
                            lean_dec_ref(v_tail_2414_);
                            return v___x_2426_;
                        }
                    } else {
                        let mut v___x_2427_: usize = 0;
                        let mut v___x_2428_: usize = 0;
                        let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec_ref_known(v___x_2419_, 1);
                        v___x_2427_ = 0usize;
                        v___x_2428_ = lean_usize_of_nat(v___x_2421_);
                        v___x_2429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_2414_, v___x_2427_, v___x_2428_, v_a_2420_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
                        lean_dec_ref(v_tail_2414_);
                        return v___x_2429_;
                    }
                }
            } else {
                lean_dec_ref(v_tail_2414_);
                return v___x_2419_;
            }
        } else {
            let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2432_: u8 = 0;
            lean_dec_ref(v_root_2413_);
            v___x_2430_ = lean_nat_sub(v_start_2398_, v_tailOff_2416_);
            lean_dec(v_tailOff_2416_);
            v___x_2431_ = lean_array_get_size(v_tail_2414_);
            v___x_2432_ = lean_nat_dec_lt(v___x_2430_, v___x_2431_);
            if v___x_2432_ == 0 {
                let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_2430_);
                lean_dec_ref(v_tail_2414_);
                v___x_2433_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2433_, 0, v_init_2397_);
                return v___x_2433_;
            } else {
                let mut v___x_2434_: u8 = 0;
                v___x_2434_ = lean_nat_dec_le(v___x_2431_, v___x_2431_);
                if v___x_2434_ == 0 {
                    if v___x_2432_ == 0 {
                        let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec(v___x_2430_);
                        lean_dec_ref(v_tail_2414_);
                        v___x_2435_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2435_, 0, v_init_2397_);
                        return v___x_2435_;
                    } else {
                        let mut v___x_2436_: usize = 0;
                        let mut v___x_2437_: usize = 0;
                        let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
                        v___x_2436_ = lean_usize_of_nat(v___x_2430_);
                        lean_dec(v___x_2430_);
                        v___x_2437_ = lean_usize_of_nat(v___x_2431_);
                        v___x_2438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_2414_, v___x_2436_, v___x_2437_, v_init_2397_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
                        lean_dec_ref(v_tail_2414_);
                        return v___x_2438_;
                    }
                } else {
                    let mut v___x_2439_: usize = 0;
                    let mut v___x_2440_: usize = 0;
                    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
                    v___x_2439_ = lean_usize_of_nat(v___x_2430_);
                    lean_dec(v___x_2430_);
                    v___x_2440_ = lean_usize_of_nat(v___x_2431_);
                    v___x_2441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_2414_, v___x_2439_, v___x_2440_, v_init_2397_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
                    lean_dec_ref(v_tail_2414_);
                    return v___x_2441_;
                }
            }
        }
    } else {
        let mut v_root_2442_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_2443_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
        v_root_2442_ = lean_ctor_get(v_t_2396_, 0);
        lean_inc_ref(v_root_2442_);
        v_tail_2443_ = lean_ctor_get(v_t_2396_, 1);
        lean_inc_ref(v_tail_2443_);
        lean_dec_ref(v_t_2396_);
        v___x_2444_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v_root_2442_, v_init_2397_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
        if lean_obj_tag(v___x_2444_) == 0 {
            let mut v_a_2445_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2447_: u8 = 0;
            v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
            lean_inc(v_a_2445_);
            v___x_2446_ = lean_array_get_size(v_tail_2443_);
            v___x_2447_ = lean_nat_dec_lt(v___x_2411_, v___x_2446_);
            if v___x_2447_ == 0 {
                lean_dec(v_a_2445_);
                lean_dec_ref(v_tail_2443_);
                return v___x_2444_;
            } else {
                let mut v___x_2448_: u8 = 0;
                v___x_2448_ = lean_nat_dec_le(v___x_2446_, v___x_2446_);
                if v___x_2448_ == 0 {
                    if v___x_2447_ == 0 {
                        lean_dec(v_a_2445_);
                        lean_dec_ref(v_tail_2443_);
                        return v___x_2444_;
                    } else {
                        let mut v___x_2449_: usize = 0;
                        let mut v___x_2450_: usize = 0;
                        let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec_ref_known(v___x_2444_, 1);
                        v___x_2449_ = 0usize;
                        v___x_2450_ = lean_usize_of_nat(v___x_2446_);
                        v___x_2451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_2443_, v___x_2449_, v___x_2450_, v_a_2445_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
                        lean_dec_ref(v_tail_2443_);
                        return v___x_2451_;
                    }
                } else {
                    let mut v___x_2452_: usize = 0;
                    let mut v___x_2453_: usize = 0;
                    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref_known(v___x_2444_, 1);
                    v___x_2452_ = 0usize;
                    v___x_2453_ = lean_usize_of_nat(v___x_2446_);
                    v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_2443_, v___x_2452_, v___x_2453_, v_a_2445_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
                    lean_dec_ref(v_tail_2443_);
                    return v___x_2454_;
                }
            }
        } else {
            lean_dec_ref(v_tail_2443_);
            return v___x_2444_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0___boxed(
    mut v_t_2455_: *mut LeanObject,
    mut v_init_2456_: *mut LeanObject,
    mut v_start_2457_: *mut LeanObject,
    mut v___y_2458_: *mut LeanObject,
    mut v___y_2459_: *mut LeanObject,
    mut v___y_2460_: *mut LeanObject,
    mut v___y_2461_: *mut LeanObject,
    mut v___y_2462_: *mut LeanObject,
    mut v___y_2463_: *mut LeanObject,
    mut v___y_2464_: *mut LeanObject,
    mut v___y_2465_: *mut LeanObject,
    mut v___y_2466_: *mut LeanObject,
    mut v___y_2467_: *mut LeanObject,
    mut v___y_2468_: *mut LeanObject,
    mut v___y_2469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2470_: *mut LeanObject = core::ptr::null_mut();
    v_res_2470_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(v_t_2455_, v_init_2456_, v_start_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
    lean_dec(v___y_2468_);
    lean_dec_ref(v___y_2467_);
    lean_dec(v___y_2466_);
    lean_dec_ref(v___y_2465_);
    lean_dec(v___y_2464_);
    lean_dec_ref(v___y_2463_);
    lean_dec(v___y_2462_);
    lean_dec_ref(v___y_2461_);
    lean_dec(v___y_2460_);
    lean_dec(v___y_2459_);
    lean_dec_ref(v___y_2458_);
    lean_dec(v_start_2457_);
    return v_res_2470_;
}
pub unsafe fn l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0(
    mut v_lctx_2471_: *mut LeanObject,
    mut v_init_2472_: *mut LeanObject,
    mut v_start_2473_: *mut LeanObject,
    mut v___y_2474_: *mut LeanObject,
    mut v___y_2475_: *mut LeanObject,
    mut v___y_2476_: *mut LeanObject,
    mut v___y_2477_: *mut LeanObject,
    mut v___y_2478_: *mut LeanObject,
    mut v___y_2479_: *mut LeanObject,
    mut v___y_2480_: *mut LeanObject,
    mut v___y_2481_: *mut LeanObject,
    mut v___y_2482_: *mut LeanObject,
    mut v___y_2483_: *mut LeanObject,
    mut v___y_2484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decls_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    v_decls_2486_ = lean_ctor_get(v_lctx_2471_, 1);
    lean_inc_ref(v_decls_2486_);
    lean_dec_ref(v_lctx_2471_);
    v___x_2487_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(v_decls_2486_, v_init_2472_, v_start_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
    return v___x_2487_;
}
pub unsafe fn l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0___boxed(
    mut v_lctx_2488_: *mut LeanObject,
    mut v_init_2489_: *mut LeanObject,
    mut v_start_2490_: *mut LeanObject,
    mut v___y_2491_: *mut LeanObject,
    mut v___y_2492_: *mut LeanObject,
    mut v___y_2493_: *mut LeanObject,
    mut v___y_2494_: *mut LeanObject,
    mut v___y_2495_: *mut LeanObject,
    mut v___y_2496_: *mut LeanObject,
    mut v___y_2497_: *mut LeanObject,
    mut v___y_2498_: *mut LeanObject,
    mut v___y_2499_: *mut LeanObject,
    mut v___y_2500_: *mut LeanObject,
    mut v___y_2501_: *mut LeanObject,
    mut v___y_2502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2503_: *mut LeanObject = core::ptr::null_mut();
    v_res_2503_ = l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0(v_lctx_2488_, v_init_2489_, v_start_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
    lean_dec(v___y_2501_);
    lean_dec_ref(v___y_2500_);
    lean_dec(v___y_2499_);
    lean_dec_ref(v___y_2498_);
    lean_dec(v___y_2497_);
    lean_dec_ref(v___y_2496_);
    lean_dec(v___y_2495_);
    lean_dec_ref(v___y_2494_);
    lean_dec(v___y_2493_);
    lean_dec(v___y_2492_);
    lean_dec_ref(v___y_2491_);
    lean_dec(v_start_2490_);
    return v_res_2503_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___lam__0(
    mut v_scope_2504_: *mut LeanObject,
    mut v___y_2505_: *mut LeanObject,
    mut v___y_2506_: *mut LeanObject,
    mut v___y_2507_: *mut LeanObject,
    mut v___y_2508_: *mut LeanObject,
    mut v___y_2509_: *mut LeanObject,
    mut v___y_2510_: *mut LeanObject,
    mut v___y_2511_: *mut LeanObject,
    mut v___y_2512_: *mut LeanObject,
    mut v___y_2513_: *mut LeanObject,
    mut v___y_2514_: *mut LeanObject,
    mut v___y_2515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextDeclIdx_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: u8 = 0;
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2526_: u8 = 0;
    let mut v_specs_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_jps_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2531_: u8 = 0;
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2538_: u8 = 0;
    let mut v_unused_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2540_: u8 = 0;
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_2517_ = lean_ctor_get(v___y_2512_, 2);
                v_decls_2518_ = lean_ctor_get(v_lctx_2517_, 1);
                v_nextDeclIdx_2519_ = lean_ctor_get(v_scope_2504_, 2);
                v_size_2520_ = lean_ctor_get(v_decls_2518_, 2);
                v___x_2521_ = lean_nat_dec_eq(v_nextDeclIdx_2519_, v_size_2520_);
                if v___x_2521_ == 0 {
                    lean_inc(v_nextDeclIdx_2519_);
                    lean_inc_ref(v_lctx_2517_);
                    v___x_2522_ = l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0(v_lctx_2517_, v_scope_2504_, v_nextDeclIdx_2519_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
                    lean_dec(v_nextDeclIdx_2519_);
                    if lean_obj_tag(v___x_2522_) == 0 {
                        v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
                        v_isSharedCheck_2540_ = (!lean_is_exclusive(v___x_2522_)) as u8;
                        if v_isSharedCheck_2540_ == 0 {
                            v___x_2525_ = v___x_2522_;
                            v_isShared_2526_ = v_isSharedCheck_2540_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2523_);
                            lean_dec(v___x_2522_);
                            v___x_2525_ = lean_box(0);
                            v_isShared_2526_ = v_isSharedCheck_2540_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_2522_;
                    }
                } else {
                    v___x_2541_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2541_, 0, v_scope_2504_);
                    return v___x_2541_;
                }
            }
            1 => {
                v_specs_2527_ = lean_ctor_get(v_a_2523_, 0);
                v_jps_2528_ = lean_ctor_get(v_a_2523_, 1);
                v_isSharedCheck_2538_ = (!lean_is_exclusive(v_a_2523_)) as u8;
                if v_isSharedCheck_2538_ == 0 {
                    v_unused_2539_ = lean_ctor_get(v_a_2523_, 2);
                    lean_dec(v_unused_2539_);
                    v___x_2530_ = v_a_2523_;
                    v_isShared_2531_ = v_isSharedCheck_2538_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_jps_2528_);
                    lean_inc(v_specs_2527_);
                    lean_dec(v_a_2523_);
                    v___x_2530_ = lean_box(0);
                    v_isShared_2531_ = v_isSharedCheck_2538_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_size_2520_);
                if v_isShared_2531_ == 0 {
                    lean_ctor_set(v___x_2530_, 2, v_size_2520_);
                    v___x_2533_ = v___x_2530_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_specs_2527_);
                    lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_jps_2528_);
                    lean_ctor_set(v_reuseFailAlloc_2537_, 2, v_size_2520_);
                    v___x_2533_ = v_reuseFailAlloc_2537_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2526_ == 0 {
                    lean_ctor_set(v___x_2525_, 0, v___x_2533_);
                    v___x_2535_ = v___x_2525_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2533_);
                    v___x_2535_ = v_reuseFailAlloc_2536_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2535_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___lam__0___boxed(
    mut v_scope_2542_: *mut LeanObject,
    mut v___y_2543_: *mut LeanObject,
    mut v___y_2544_: *mut LeanObject,
    mut v___y_2545_: *mut LeanObject,
    mut v___y_2546_: *mut LeanObject,
    mut v___y_2547_: *mut LeanObject,
    mut v___y_2548_: *mut LeanObject,
    mut v___y_2549_: *mut LeanObject,
    mut v___y_2550_: *mut LeanObject,
    mut v___y_2551_: *mut LeanObject,
    mut v___y_2552_: *mut LeanObject,
    mut v___y_2553_: *mut LeanObject,
    mut v___y_2554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2555_: *mut LeanObject = core::ptr::null_mut();
    v_res_2555_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___lam__0(
        v_scope_2542_,
        v___y_2543_,
        v___y_2544_,
        v___y_2545_,
        v___y_2546_,
        v___y_2547_,
        v___y_2548_,
        v___y_2549_,
        v___y_2550_,
        v___y_2551_,
        v___y_2552_,
        v___y_2553_,
    );
    lean_dec(v___y_2553_);
    lean_dec_ref(v___y_2552_);
    lean_dec(v___y_2551_);
    lean_dec_ref(v___y_2550_);
    lean_dec(v___y_2549_);
    lean_dec_ref(v___y_2548_);
    lean_dec(v___y_2547_);
    lean_dec_ref(v___y_2546_);
    lean_dec(v___y_2545_);
    lean_dec(v___y_2544_);
    lean_dec_ref(v___y_2543_);
    return v_res_2555_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs(
    mut v_scope_2556_: *mut LeanObject,
    mut v_goal_2557_: *mut LeanObject,
    mut v_a_2558_: *mut LeanObject,
    mut v_a_2559_: *mut LeanObject,
    mut v_a_2560_: *mut LeanObject,
    mut v_a_2561_: *mut LeanObject,
    mut v_a_2562_: *mut LeanObject,
    mut v_a_2563_: *mut LeanObject,
    mut v_a_2564_: *mut LeanObject,
    mut v_a_2565_: *mut LeanObject,
    mut v_a_2566_: *mut LeanObject,
    mut v_a_2567_: *mut LeanObject,
    mut v_a_2568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    v___f_2570_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___lam__0___boxed
            as *mut core::ffi::c_void,
        13,
        1,
    );
    lean_closure_set(v___f_2570_, 0, v_scope_2556_);
    v___x_2571_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_goal_2557_, v___f_2570_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
    return v___x_2571_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___boxed(
    mut v_scope_2572_: *mut LeanObject,
    mut v_goal_2573_: *mut LeanObject,
    mut v_a_2574_: *mut LeanObject,
    mut v_a_2575_: *mut LeanObject,
    mut v_a_2576_: *mut LeanObject,
    mut v_a_2577_: *mut LeanObject,
    mut v_a_2578_: *mut LeanObject,
    mut v_a_2579_: *mut LeanObject,
    mut v_a_2580_: *mut LeanObject,
    mut v_a_2581_: *mut LeanObject,
    mut v_a_2582_: *mut LeanObject,
    mut v_a_2583_: *mut LeanObject,
    mut v_a_2584_: *mut LeanObject,
    mut v_a_2585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2586_: *mut LeanObject = core::ptr::null_mut();
    v_res_2586_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs(
        v_scope_2572_,
        v_goal_2573_,
        v_a_2574_,
        v_a_2575_,
        v_a_2576_,
        v_a_2577_,
        v_a_2578_,
        v_a_2579_,
        v_a_2580_,
        v_a_2581_,
        v_a_2582_,
        v_a_2583_,
        v_a_2584_,
    );
    lean_dec(v_a_2584_);
    lean_dec_ref(v_a_2583_);
    lean_dec(v_a_2582_);
    lean_dec_ref(v_a_2581_);
    lean_dec(v_a_2580_);
    lean_dec_ref(v_a_2579_);
    lean_dec(v_a_2578_);
    lean_dec_ref(v_a_2577_);
    lean_dec(v_a_2576_);
    lean_dec(v_a_2575_);
    lean_dec_ref(v_a_2574_);
    return v_res_2586_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(
    mut v_as_2587_: *mut LeanObject,
    mut v_i_2588_: usize,
    mut v_stop_2589_: usize,
    mut v_b_2590_: *mut LeanObject,
    mut v___y_2591_: *mut LeanObject,
    mut v___y_2592_: *mut LeanObject,
    mut v___y_2593_: *mut LeanObject,
    mut v___y_2594_: *mut LeanObject,
    mut v___y_2595_: *mut LeanObject,
    mut v___y_2596_: *mut LeanObject,
    mut v___y_2597_: *mut LeanObject,
    mut v___y_2598_: *mut LeanObject,
    mut v___y_2599_: *mut LeanObject,
    mut v___y_2600_: *mut LeanObject,
    mut v___y_2601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    v___x_2603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_as_2587_, v_i_2588_, v_stop_2589_, v_b_2590_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
    return v___x_2603_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___boxed(
    mut v_as_2604_: *mut LeanObject,
    mut v_i_2605_: *mut LeanObject,
    mut v_stop_2606_: *mut LeanObject,
    mut v_b_2607_: *mut LeanObject,
    mut v___y_2608_: *mut LeanObject,
    mut v___y_2609_: *mut LeanObject,
    mut v___y_2610_: *mut LeanObject,
    mut v___y_2611_: *mut LeanObject,
    mut v___y_2612_: *mut LeanObject,
    mut v___y_2613_: *mut LeanObject,
    mut v___y_2614_: *mut LeanObject,
    mut v___y_2615_: *mut LeanObject,
    mut v___y_2616_: *mut LeanObject,
    mut v___y_2617_: *mut LeanObject,
    mut v___y_2618_: *mut LeanObject,
    mut v___y_2619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2620_: usize = 0;
    let mut v_stop_boxed_2621_: usize = 0;
    let mut v_res_2622_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2620_ = lean_unbox_usize(v_i_2605_);
    lean_dec(v_i_2605_);
    v_stop_boxed_2621_ = lean_unbox_usize(v_stop_2606_);
    lean_dec(v_stop_2606_);
    v_res_2622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(v_as_2604_, v_i_boxed_2620_, v_stop_boxed_2621_, v_b_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
    lean_dec(v___y_2618_);
    lean_dec_ref(v___y_2617_);
    lean_dec(v___y_2616_);
    lean_dec_ref(v___y_2615_);
    lean_dec(v___y_2614_);
    lean_dec_ref(v___y_2613_);
    lean_dec(v___y_2612_);
    lean_dec_ref(v___y_2611_);
    lean_dec(v___y_2610_);
    lean_dec(v___y_2609_);
    lean_dec_ref(v___y_2608_);
    lean_dec_ref(v_as_2604_);
    return v_res_2622_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(
    mut v_a_2623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fuel_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2630_: u8 = 0;
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: u8 = 0;
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2637_: u8 = 0;
    let mut v___x_2638_: u8 = 0;
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2625_ = lean_st_ref_get(v_a_2623_);
                v_fuel_2626_ = lean_ctor_get(v___x_2625_, 5);
                lean_inc(v_fuel_2626_);
                lean_dec(v___x_2625_);
                if lean_obj_tag(v_fuel_2626_) == 0 {
                    v_n_2627_ = lean_ctor_get(v_fuel_2626_, 0);
                    v_isSharedCheck_2637_ = (!lean_is_exclusive(v_fuel_2626_)) as u8;
                    if v_isSharedCheck_2637_ == 0 {
                        v___x_2629_ = v_fuel_2626_;
                        v_isShared_2630_ = v_isSharedCheck_2637_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_n_2627_);
                        lean_dec(v_fuel_2626_);
                        v___x_2629_ = lean_box(0);
                        v_isShared_2630_ = v_isSharedCheck_2637_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_fuel_2626_);
                    v___x_2638_ = 0;
                    v___x_2639_ = lean_box((v___x_2638_) as usize);
                    v___x_2640_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2640_, 0, v___x_2639_);
                    return v___x_2640_;
                }
            }
            1 => {
                v___x_2631_ = lean_unsigned_to_nat(0);
                v___x_2632_ = lean_nat_dec_eq(v_n_2627_, v___x_2631_);
                lean_dec(v_n_2627_);
                v___x_2633_ = lean_box((v___x_2632_) as usize);
                if v_isShared_2630_ == 0 {
                    lean_ctor_set(v___x_2629_, 0, v___x_2633_);
                    v___x_2635_ = v___x_2629_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
                    v___x_2635_ = v_reuseFailAlloc_2636_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2635_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg___boxed(
    mut v_a_2641_: *mut LeanObject,
    mut v_a_2642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2643_: *mut LeanObject = core::ptr::null_mut();
    v_res_2643_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v_a_2641_);
    lean_dec(v_a_2641_);
    return v_res_2643_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel(
    mut v_a_2644_: *mut LeanObject,
    mut v_a_2645_: *mut LeanObject,
    mut v_a_2646_: *mut LeanObject,
    mut v_a_2647_: *mut LeanObject,
    mut v_a_2648_: *mut LeanObject,
    mut v_a_2649_: *mut LeanObject,
    mut v_a_2650_: *mut LeanObject,
    mut v_a_2651_: *mut LeanObject,
    mut v_a_2652_: *mut LeanObject,
    mut v_a_2653_: *mut LeanObject,
    mut v_a_2654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    v___x_2656_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v_a_2645_);
    return v___x_2656_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___boxed(
    mut v_a_2657_: *mut LeanObject,
    mut v_a_2658_: *mut LeanObject,
    mut v_a_2659_: *mut LeanObject,
    mut v_a_2660_: *mut LeanObject,
    mut v_a_2661_: *mut LeanObject,
    mut v_a_2662_: *mut LeanObject,
    mut v_a_2663_: *mut LeanObject,
    mut v_a_2664_: *mut LeanObject,
    mut v_a_2665_: *mut LeanObject,
    mut v_a_2666_: *mut LeanObject,
    mut v_a_2667_: *mut LeanObject,
    mut v_a_2668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2669_: *mut LeanObject = core::ptr::null_mut();
    v_res_2669_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel(
        v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_,
        v_a_2665_, v_a_2666_, v_a_2667_,
    );
    lean_dec(v_a_2667_);
    lean_dec_ref(v_a_2666_);
    lean_dec(v_a_2665_);
    lean_dec_ref(v_a_2664_);
    lean_dec(v_a_2663_);
    lean_dec_ref(v_a_2662_);
    lean_dec(v_a_2661_);
    lean_dec_ref(v_a_2660_);
    lean_dec(v_a_2659_);
    lean_dec(v_a_2658_);
    lean_dec_ref(v_a_2657_);
    return v_res_2669_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(
    mut v_a_2670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_specBackwardRuleCache_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_splitBackwardRuleCache_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invariants_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vcs_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simpState_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fuel_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inlineHandledInvariants_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_preTacFailed_2680_: u8 = 0;
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2683_: u8 = 0;
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_2694_: u8 = 0;
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2697_: u8 = 0;
    let mut v_one_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2703_: u8 = 0;
    let mut v_unused_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2672_ = lean_st_ref_take(v_a_2670_);
                v_specBackwardRuleCache_2673_ = lean_ctor_get(v___x_2672_, 0);
                v_splitBackwardRuleCache_2674_ = lean_ctor_get(v___x_2672_, 1);
                v_invariants_2675_ = lean_ctor_get(v___x_2672_, 2);
                v_vcs_2676_ = lean_ctor_get(v___x_2672_, 3);
                v_simpState_2677_ = lean_ctor_get(v___x_2672_, 4);
                v_fuel_2678_ = lean_ctor_get(v___x_2672_, 5);
                v_inlineHandledInvariants_2679_ = lean_ctor_get(v___x_2672_, 6);
                v_preTacFailed_2680_ = lean_ctor_get_uint8(
                    v___x_2672_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_isSharedCheck_2705_ = (!lean_is_exclusive(v___x_2672_)) as u8;
                if v_isSharedCheck_2705_ == 0 {
                    v___x_2682_ = v___x_2672_;
                    v_isShared_2683_ = v_isSharedCheck_2705_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_inlineHandledInvariants_2679_);
                    lean_inc(v_fuel_2678_);
                    lean_inc(v_simpState_2677_);
                    lean_inc(v_vcs_2676_);
                    lean_inc(v_invariants_2675_);
                    lean_inc(v_splitBackwardRuleCache_2674_);
                    lean_inc(v_specBackwardRuleCache_2673_);
                    lean_dec(v___x_2672_);
                    v___x_2682_ = lean_box(0);
                    v_isShared_2683_ = v_isSharedCheck_2705_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2684_ = lean_box(0);
                if lean_obj_tag(v_fuel_2678_) == 0 {
                    v_n_2692_ = lean_ctor_get(v_fuel_2678_, 0);
                    v_zero_2693_ = lean_unsigned_to_nat(0);
                    v_isZero_2694_ = lean_nat_dec_eq(v_n_2692_, v_zero_2693_);
                    if v_isZero_2694_ == 0 {
                        lean_inc(v_n_2692_);
                        v_isSharedCheck_2703_ = (!lean_is_exclusive(v_fuel_2678_)) as u8;
                        if v_isSharedCheck_2703_ == 0 {
                            v_unused_2704_ = lean_ctor_get(v_fuel_2678_, 0);
                            lean_dec(v_unused_2704_);
                            v___x_2696_ = v_fuel_2678_;
                            v_isShared_2697_ = v_isSharedCheck_2703_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec(v_fuel_2678_);
                            v___x_2696_ = lean_box(0);
                            v_isShared_2697_ = v_isSharedCheck_2703_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___y_2686_ = v_fuel_2678_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___y_2686_ = v_fuel_2678_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2683_ == 0 {
                    lean_ctor_set(v___x_2682_, 5, v___y_2686_);
                    v___x_2688_ = v___x_2682_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_specBackwardRuleCache_2673_);
                    lean_ctor_set(v_reuseFailAlloc_2691_, 1, v_splitBackwardRuleCache_2674_);
                    lean_ctor_set(v_reuseFailAlloc_2691_, 2, v_invariants_2675_);
                    lean_ctor_set(v_reuseFailAlloc_2691_, 3, v_vcs_2676_);
                    lean_ctor_set(v_reuseFailAlloc_2691_, 4, v_simpState_2677_);
                    lean_ctor_set(v_reuseFailAlloc_2691_, 5, v___y_2686_);
                    lean_ctor_set(v_reuseFailAlloc_2691_, 6, v_inlineHandledInvariants_2679_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2691_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v_preTacFailed_2680_,
                    );
                    v___x_2688_ = v_reuseFailAlloc_2691_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2689_ = lean_st_ref_set(v_a_2670_, v___x_2688_);
                v___x_2690_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2690_, 0, v___x_2684_);
                return v___x_2690_;
            }
            4 => {
                v_one_2698_ = lean_unsigned_to_nat(1);
                v_n_2699_ = lean_nat_sub(v_n_2692_, v_one_2698_);
                lean_dec(v_n_2692_);
                if v_isShared_2697_ == 0 {
                    lean_ctor_set(v___x_2696_, 0, v_n_2699_);
                    v___x_2701_ = v___x_2696_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_n_2699_);
                    v___x_2701_ = v_reuseFailAlloc_2702_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_2686_ = v___x_2701_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg___boxed(
    mut v_a_2706_: *mut LeanObject,
    mut v_a_2707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2708_: *mut LeanObject = core::ptr::null_mut();
    v_res_2708_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v_a_2706_);
    lean_dec(v_a_2706_);
    return v_res_2708_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne(
    mut v_a_2709_: *mut LeanObject,
    mut v_a_2710_: *mut LeanObject,
    mut v_a_2711_: *mut LeanObject,
    mut v_a_2712_: *mut LeanObject,
    mut v_a_2713_: *mut LeanObject,
    mut v_a_2714_: *mut LeanObject,
    mut v_a_2715_: *mut LeanObject,
    mut v_a_2716_: *mut LeanObject,
    mut v_a_2717_: *mut LeanObject,
    mut v_a_2718_: *mut LeanObject,
    mut v_a_2719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    v___x_2721_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v_a_2710_);
    return v___x_2721_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___boxed(
    mut v_a_2722_: *mut LeanObject,
    mut v_a_2723_: *mut LeanObject,
    mut v_a_2724_: *mut LeanObject,
    mut v_a_2725_: *mut LeanObject,
    mut v_a_2726_: *mut LeanObject,
    mut v_a_2727_: *mut LeanObject,
    mut v_a_2728_: *mut LeanObject,
    mut v_a_2729_: *mut LeanObject,
    mut v_a_2730_: *mut LeanObject,
    mut v_a_2731_: *mut LeanObject,
    mut v_a_2732_: *mut LeanObject,
    mut v_a_2733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2734_: *mut LeanObject = core::ptr::null_mut();
    v_res_2734_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne(
        v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_,
        v_a_2730_, v_a_2731_, v_a_2732_,
    );
    lean_dec(v_a_2732_);
    lean_dec_ref(v_a_2731_);
    lean_dec(v_a_2730_);
    lean_dec_ref(v_a_2729_);
    lean_dec(v_a_2728_);
    lean_dec_ref(v_a_2727_);
    lean_dec(v_a_2726_);
    lean_dec_ref(v_a_2725_);
    lean_dec(v_a_2724_);
    lean_dec(v_a_2723_);
    lean_dec_ref(v_a_2722_);
    return v_res_2734_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Apply(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default =
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default();
    lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default);
    l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope =
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope();
    lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_VCGen_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Apply(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
}
