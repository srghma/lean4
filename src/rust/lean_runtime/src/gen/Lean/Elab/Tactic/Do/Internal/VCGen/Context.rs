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
    lean_array_push, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__4___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__1_value: crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 105, 110, 115, 101, 114, 116, 75, 101, 121, 86, 97, 108, 117, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__2_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 107, 101, 121, 32, 115, 101, 113, 117, 101, 110, 99, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorIdx(
    mut v_x_1368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1368_) {
        0 => {
            let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1369_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1369_;
        }
        1 => {
            let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1370_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1370_;
        }
        _ => {
            let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1371_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1371_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorIdx___boxed(
    mut v_x_1372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1373_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorIdx(v_x_1372_);
    crate::leanh::lean_dec(v_x_1372_);
    return v_res_1373_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(
    mut v_t_1374_: *mut crate::leanh::LeanObject,
    mut v_k_1375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_1374_) {
        0 => {
            return v_k_1375_;
        }
        1 => {
            let mut v_silent_1376_: u8 = 0;
            let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_silent_1376_ = crate::leanh::lean_ctor_get_uint8(v_t_1374_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_t_1374_, 0);
            v___x_1377_ = crate::leanh::lean_box((v_silent_1376_) as usize);
            v___x_1378_ = crate::leanh::lean_apply_1(v_k_1375_, v___x_1377_);
            return v___x_1378_;
        }
        _ => {
            let mut v_tac_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_tac_1379_ = crate::leanh::lean_ctor_get(v_t_1374_, 0);
            crate::leanh::lean_inc(v_tac_1379_);
            crate::leanh::lean_dec_ref_known(v_t_1374_, 1);
            v___x_1380_ = crate::leanh::lean_apply_1(v_k_1375_, v_tac_1379_);
            return v___x_1380_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim(
    mut v_motive_1381_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1382_: *mut crate::leanh::LeanObject,
    mut v_t_1383_: *mut crate::leanh::LeanObject,
    mut v_h_1384_: *mut crate::leanh::LeanObject,
    mut v_k_1385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1386_ =
        l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_1383_, v_k_1385_);
    return v___x_1386_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___boxed(
    mut v_motive_1387_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1388_: *mut crate::leanh::LeanObject,
    mut v_t_1389_: *mut crate::leanh::LeanObject,
    mut v_h_1390_: *mut crate::leanh::LeanObject,
    mut v_k_1391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1392_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim(
        v_motive_1387_,
        v_ctorIdx_1388_,
        v_t_1389_,
        v_h_1390_,
        v_k_1391_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1388_);
    return v_res_1392_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_none_elim___redArg(
    mut v_t_1393_: *mut crate::leanh::LeanObject,
    mut v_none_1394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1395_ =
        l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_1393_, v_none_1394_);
    return v___x_1395_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_none_elim(
    mut v_motive_1396_: *mut crate::leanh::LeanObject,
    mut v_t_1397_: *mut crate::leanh::LeanObject,
    mut v_h_1398_: *mut crate::leanh::LeanObject,
    mut v_none_1399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1400_ =
        l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_1397_, v_none_1399_);
    return v___x_1400_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_grind_elim___redArg(
    mut v_t_1401_: *mut crate::leanh::LeanObject,
    mut v_grind_1402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1403_ =
        l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_1401_, v_grind_1402_);
    return v___x_1403_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_grind_elim(
    mut v_motive_1404_: *mut crate::leanh::LeanObject,
    mut v_t_1405_: *mut crate::leanh::LeanObject,
    mut v_h_1406_: *mut crate::leanh::LeanObject,
    mut v_grind_1407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1408_ =
        l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_1405_, v_grind_1407_);
    return v___x_1408_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_tactic_elim___redArg(
    mut v_t_1409_: *mut crate::leanh::LeanObject,
    mut v_tactic_1410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1411_ =
        l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_1409_, v_tactic_1410_);
    return v___x_1411_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_tactic_elim(
    mut v_motive_1412_: *mut crate::leanh::LeanObject,
    mut v_t_1413_: *mut crate::leanh::LeanObject,
    mut v_h_1414_: *mut crate::leanh::LeanObject,
    mut v_tactic_1415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1416_ =
        l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_ctorElim___redArg(v_t_1413_, v_tactic_1415_);
    return v___x_1416_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_isGrind(
    mut v_x_1417_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1417_) == 1 {
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
    mut v_x_1420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1421_: u8 = 0;
    let mut v_r_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1421_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_isGrind(v_x_1420_);
    crate::leanh::lean_dec(v_x_1420_);
    v_r_1422_ = crate::leanh::lean_box((v_res_1421_) as usize);
    return v_r_1422_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1423_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1424_ = crate::leanh::lean_box(1);
    v___x_1425_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default;
    v___x_1426_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1426_, 0, v___x_1425_);
    crate::leanh::lean_ctor_set(v___x_1426_, 1, v___x_1424_);
    crate::leanh::lean_ctor_set(v___x_1426_, 2, v___x_1423_);
    return v___x_1426_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1427_ = crate::leanh::lean_obj_once(
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
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1428_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default;
    return v___x_1428_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_registerJP(
    mut v_s_1429_: *mut crate::leanh::LeanObject,
    mut v_fv_1430_: *mut crate::leanh::LeanObject,
    mut v_info_1431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_specs_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextDeclIdx_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1437_: u8 = 0;
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1442_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_specs_1432_ = crate::leanh::lean_ctor_get(v_s_1429_, 0);
                v_jps_1433_ = crate::leanh::lean_ctor_get(v_s_1429_, 1);
                v_nextDeclIdx_1434_ = crate::leanh::lean_ctor_get(v_s_1429_, 2);
                v_isSharedCheck_1442_ = (!crate::leanh::lean_is_exclusive(v_s_1429_)) as u8;
                if v_isSharedCheck_1442_ == 0 {
                    v___x_1436_ = v_s_1429_;
                    v_isShared_1437_ = v_isSharedCheck_1442_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextDeclIdx_1434_);
                    crate::leanh::lean_inc(v_jps_1433_);
                    crate::leanh::lean_inc(v_specs_1432_);
                    crate::leanh::lean_dec(v_s_1429_);
                    v___x_1436_ = crate::leanh::lean_box(0);
                    v_isShared_1437_ = v_isSharedCheck_1442_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1438_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fv_1430_, v_info_1431_, v_jps_1433_);
                if v_isShared_1437_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1436_, 1, v___x_1438_);
                    v___x_1440_ = v___x_1436_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1441_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_specs_1432_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1441_, 1, v___x_1438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1441_, 2, v_nextDeclIdx_1434_);
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
    mut v_t_1443_: *mut crate::leanh::LeanObject,
    mut v_k_1444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u8 = 0;
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1443_) == 0 {
                    v_k_1445_ = crate::leanh::lean_ctor_get(v_t_1443_, 1);
                    v_v_1446_ = crate::leanh::lean_ctor_get(v_t_1443_, 2);
                    v_l_1447_ = crate::leanh::lean_ctor_get(v_t_1443_, 3);
                    v_r_1448_ = crate::leanh::lean_ctor_get(v_t_1443_, 4);
                    v___x_1449_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1444_, v_k_1445_);
                    match v___x_1449_ {
                        0 => {
                            v_t_1443_ = v_l_1447_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_1446_);
                            v___x_1451_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1451_, 0, v_v_1446_);
                            return v___x_1451_;
                        }
                        _ => {
                            v_t_1443_ = v_r_1448_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1453_ = crate::leanh::lean_box(0);
                    return v___x_1453_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg___boxed(
    mut v_t_1454_: *mut crate::leanh::LeanObject,
    mut v_k_1455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1456_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_t_1454_, v_k_1455_);
    crate::leanh::lean_dec(v_k_1455_);
    crate::leanh::lean_dec(v_t_1454_);
    return v_res_1456_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f(
    mut v_s_1457_: *mut crate::leanh::LeanObject,
    mut v_fv_1458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_jps_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_jps_1459_ = crate::leanh::lean_ctor_get(v_s_1457_, 1);
    v___x_1460_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_jps_1459_, v_fv_1458_);
    return v___x_1460_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f___boxed(
    mut v_s_1461_: *mut crate::leanh::LeanObject,
    mut v_fv_1462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1463_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f(v_s_1461_, v_fv_1462_);
    crate::leanh::lean_dec(v_fv_1462_);
    crate::leanh::lean_dec_ref(v_s_1461_);
    return v_res_1463_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0(
    mut v_00_u03b4_1464_: *mut crate::leanh::LeanObject,
    mut v_t_1465_: *mut crate::leanh::LeanObject,
    mut v_k_1466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1467_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_t_1465_, v_k_1466_);
    return v___x_1467_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___boxed(
    mut v_00_u03b4_1468_: *mut crate::leanh::LeanObject,
    mut v_t_1469_: *mut crate::leanh::LeanObject,
    mut v_k_1470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1471_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0(v_00_u03b4_1468_, v_t_1469_, v_k_1470_);
    crate::leanh::lean_dec(v_k_1470_);
    crate::leanh::lean_dec(v_t_1469_);
    return v_res_1471_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__7_spec__9___redArg(
    mut v_x_1472_: *mut crate::leanh::LeanObject,
    mut v_x_1473_: *mut crate::leanh::LeanObject,
    mut v_x_1474_: *mut crate::leanh::LeanObject,
    mut v_x_1475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1480_: u8 = 0;
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: u8 = 0;
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: u8 = 0;
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1501_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1476_ = crate::leanh::lean_ctor_get(v_x_1472_, 0);
                v_vs_1477_ = crate::leanh::lean_ctor_get(v_x_1472_, 1);
                v_isSharedCheck_1501_ = (!crate::leanh::lean_is_exclusive(v_x_1472_)) as u8;
                if v_isSharedCheck_1501_ == 0 {
                    v___x_1479_ = v_x_1472_;
                    v_isShared_1480_ = v_isSharedCheck_1501_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1477_);
                    crate::leanh::lean_inc(v_ks_1476_);
                    crate::leanh::lean_dec(v_x_1472_);
                    v___x_1479_ = crate::leanh::lean_box(0);
                    v_isShared_1480_ = v_isSharedCheck_1501_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1481_ = lean_array_get_size(v_ks_1476_);
                v___x_1482_ = lean_nat_dec_lt(v_x_1473_, v___x_1481_);
                if v___x_1482_ == 0 {
                    crate::leanh::lean_dec(v_x_1473_);
                    v___x_1483_ = lean_array_push(v_ks_1476_, v_x_1474_);
                    v___x_1484_ = lean_array_push(v_vs_1477_, v_x_1475_);
                    if v_isShared_1480_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1479_, 1, v___x_1484_);
                        crate::leanh::lean_ctor_set(v___x_1479_, 0, v___x_1483_);
                        v___x_1486_ = v___x_1479_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1487_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1483_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 1, v___x_1484_);
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
                            v_reuseFailAlloc_1495_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_ks_1476_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_vs_1477_);
                            v___x_1491_ = v_reuseFailAlloc_1495_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1496_ = lean_array_fset(v_ks_1476_, v_x_1473_, v_x_1474_);
                        v___x_1497_ = lean_array_fset(v_vs_1477_, v_x_1473_, v_x_1475_);
                        crate::leanh::lean_dec(v_x_1473_);
                        if v_isShared_1480_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1479_, 1, v___x_1497_);
                            crate::leanh::lean_ctor_set(v___x_1479_, 0, v___x_1496_);
                            v___x_1499_ = v___x_1479_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1500_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1496_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 1, v___x_1497_);
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
                v___x_1492_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1493_ = lean_nat_add(v_x_1473_, v___x_1492_);
                crate::leanh::lean_dec(v_x_1473_);
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
    mut v_n_1502_: *mut crate::leanh::LeanObject,
    mut v_k_1503_: *mut crate::leanh::LeanObject,
    mut v_v_1504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1505_ = crate::leanh::lean_unsigned_to_nat(0);
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
    v___x_1511_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__0);
    v___x_1512_ = lean_usize_sub(v___x_1511_, v___x_1510_);
    return v___x_1512_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1513_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1513_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_x_1514_: *mut crate::leanh::LeanObject,
    mut v_x_1515_: usize,
    mut v_x_1516_: usize,
    mut v_x_1517_: *mut crate::leanh::LeanObject,
    mut v_x_1518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: usize = 0;
    let mut v___x_1521_: usize = 0;
    let mut v___x_1522_: usize = 0;
    let mut v___x_1523_: usize = 0;
    let mut v_j_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: u8 = 0;
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1529_: u8 = 0;
    let mut v_v_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1543_: u8 = 0;
    let mut v___x_1544_: u8 = 0;
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1550_: u8 = 0;
    let mut v_node_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1554_: u8 = 0;
    let mut v___x_1555_: usize = 0;
    let mut v___x_1556_: usize = 0;
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1561_: u8 = 0;
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1563_: u8 = 0;
    let mut v_unused_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1569_: u8 = 0;
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1574_: u8 = 0;
    let mut v_ks_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: usize = 0;
    let mut v___x_1581_: u8 = 0;
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: u8 = 0;
    let mut v_reuseFailAlloc_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1586_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1514_) == 0 {
                    v_es_1519_ = crate::leanh::lean_ctor_get(v_x_1514_, 0);
                    v___x_1520_ = 5usize;
                    v___x_1521_ = 1usize;
                    v___x_1522_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__1);
                    v___x_1523_ = lean_usize_land(v_x_1515_, v___x_1522_);
                    v_j_1524_ = lean_usize_to_nat(v___x_1523_);
                    v___x_1525_ = lean_array_get_size(v_es_1519_);
                    v___x_1526_ = lean_nat_dec_lt(v_j_1524_, v___x_1525_);
                    if v___x_1526_ == 0 {
                        crate::leanh::lean_dec(v_j_1524_);
                        crate::leanh::lean_dec(v_x_1518_);
                        crate::leanh::lean_dec(v_x_1517_);
                        return v_x_1514_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1519_);
                        v_isSharedCheck_1563_ = (!crate::leanh::lean_is_exclusive(v_x_1514_)) as u8;
                        if v_isSharedCheck_1563_ == 0 {
                            v_unused_1564_ = crate::leanh::lean_ctor_get(v_x_1514_, 0);
                            crate::leanh::lean_dec(v_unused_1564_);
                            v___x_1528_ = v_x_1514_;
                            v_isShared_1529_ = v_isSharedCheck_1563_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1514_);
                            v___x_1528_ = crate::leanh::lean_box(0);
                            v_isShared_1529_ = v_isSharedCheck_1563_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1565_ = crate::leanh::lean_ctor_get(v_x_1514_, 0);
                    v_vs_1566_ = crate::leanh::lean_ctor_get(v_x_1514_, 1);
                    v_isSharedCheck_1586_ = (!crate::leanh::lean_is_exclusive(v_x_1514_)) as u8;
                    if v_isSharedCheck_1586_ == 0 {
                        v___x_1568_ = v_x_1514_;
                        v_isShared_1569_ = v_isSharedCheck_1586_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1566_);
                        crate::leanh::lean_inc(v_ks_1565_);
                        crate::leanh::lean_dec(v_x_1514_);
                        v___x_1568_ = crate::leanh::lean_box(0);
                        v_isShared_1569_ = v_isSharedCheck_1586_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1530_ = lean_array_fget(v_es_1519_, v_j_1524_);
                v___x_1531_ = crate::leanh::lean_box(0);
                v_xs_x27_1532_ = lean_array_fset(v_es_1519_, v_j_1524_, v___x_1531_);
                match crate::leanh::lean_obj_tag(v_v_1530_) {
                    0 => {
                        v_key_1539_ = crate::leanh::lean_ctor_get(v_v_1530_, 0);
                        v_val_1540_ = crate::leanh::lean_ctor_get(v_v_1530_, 1);
                        v_isSharedCheck_1550_ = (!crate::leanh::lean_is_exclusive(v_v_1530_)) as u8;
                        if v_isSharedCheck_1550_ == 0 {
                            v___x_1542_ = v_v_1530_;
                            v_isShared_1543_ = v_isSharedCheck_1550_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1540_);
                            crate::leanh::lean_inc(v_key_1539_);
                            crate::leanh::lean_dec(v_v_1530_);
                            v___x_1542_ = crate::leanh::lean_box(0);
                            v_isShared_1543_ = v_isSharedCheck_1550_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1551_ = crate::leanh::lean_ctor_get(v_v_1530_, 0);
                        v_isSharedCheck_1561_ = (!crate::leanh::lean_is_exclusive(v_v_1530_)) as u8;
                        if v_isSharedCheck_1561_ == 0 {
                            v___x_1553_ = v_v_1530_;
                            v_isShared_1554_ = v_isSharedCheck_1561_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1551_);
                            crate::leanh::lean_dec(v_v_1530_);
                            v___x_1553_ = crate::leanh::lean_box(0);
                            v_isShared_1554_ = v_isSharedCheck_1561_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1562_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1562_, 0, v_x_1517_);
                        crate::leanh::lean_ctor_set(v___x_1562_, 1, v_x_1518_);
                        v___y_1534_ = v___x_1562_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1535_ = lean_array_fset(v_xs_x27_1532_, v_j_1524_, v___y_1534_);
                crate::leanh::lean_dec(v_j_1524_);
                if v_isShared_1529_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1528_, 0, v___x_1535_);
                    v___x_1537_ = v___x_1528_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1538_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1535_);
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
                    crate::leanh::lean_del_object(v___x_1542_);
                    v___x_1545_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1539_,
                        v_val_1540_,
                        v_x_1517_,
                        v_x_1518_,
                    );
                    v___x_1546_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1546_, 0, v___x_1545_);
                    v___y_1534_ = v___x_1546_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1540_);
                    crate::leanh::lean_dec(v_key_1539_);
                    if v_isShared_1543_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1542_, 1, v_x_1518_);
                        crate::leanh::lean_ctor_set(v___x_1542_, 0, v_x_1517_);
                        v___x_1548_ = v___x_1542_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1549_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_x_1517_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_x_1518_);
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
                    crate::leanh::lean_ctor_set(v___x_1553_, 0, v___x_1557_);
                    v___x_1559_ = v___x_1553_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1560_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
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
                    v_reuseFailAlloc_1585_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_ks_1565_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_vs_1566_);
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
                    v___x_1583_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1584_ = lean_nat_dec_lt(v___x_1582_, v___x_1583_);
                    crate::leanh::lean_dec(v___x_1582_);
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
                    v_ks_1575_ = crate::leanh::lean_ctor_get(v_newNode_1572_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1575_);
                    v_vs_1576_ = crate::leanh::lean_ctor_get(v_newNode_1572_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1576_);
                    crate::leanh::lean_dec_ref(v_newNode_1572_);
                    v___x_1577_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1578_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__2);
                    v___x_1579_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__8___redArg(v_x_1516_, v_ks_1575_, v_vs_1576_, v___x_1577_, v___x_1578_);
                    crate::leanh::lean_dec_ref(v_vs_1576_);
                    crate::leanh::lean_dec_ref(v_ks_1575_);
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
    mut v_keys_1588_: *mut crate::leanh::LeanObject,
    mut v_vals_1589_: *mut crate::leanh::LeanObject,
    mut v_i_1590_: *mut crate::leanh::LeanObject,
    mut v_entries_1591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: u8 = 0;
    let mut v_k_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: u64 = 0;
    let mut v_h_1597_: usize = 0;
    let mut v___x_1598_: usize = 0;
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: usize = 0;
    let mut v___x_1601_: usize = 0;
    let mut v___x_1602_: usize = 0;
    let mut v_h_1603_: usize = 0;
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1592_ = lean_array_get_size(v_keys_1588_);
                v___x_1593_ = lean_nat_dec_lt(v_i_1590_, v___x_1592_);
                if v___x_1593_ == 0 {
                    crate::leanh::lean_dec(v_i_1590_);
                    return v_entries_1591_;
                } else {
                    v_k_1594_ = lean_array_fget_borrowed(v_keys_1588_, v_i_1590_);
                    v_v_1595_ = lean_array_fget_borrowed(v_vals_1589_, v_i_1590_);
                    v___x_1596_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_1594_);
                    v_h_1597_ = lean_uint64_to_usize(v___x_1596_);
                    v___x_1598_ = 5usize;
                    v___x_1599_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1600_ = 1usize;
                    v___x_1601_ = lean_usize_sub(v_depth_1587_, v___x_1600_);
                    v___x_1602_ = lean_usize_mul(v___x_1598_, v___x_1601_);
                    v_h_1603_ = lean_usize_shift_right(v_h_1597_, v___x_1602_);
                    v___x_1604_ = lean_nat_add(v_i_1590_, v___x_1599_);
                    crate::leanh::lean_dec(v_i_1590_);
                    crate::leanh::lean_inc(v_v_1595_);
                    crate::leanh::lean_inc(v_k_1594_);
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
    mut v_depth_1607_: *mut crate::leanh::LeanObject,
    mut v_keys_1608_: *mut crate::leanh::LeanObject,
    mut v_vals_1609_: *mut crate::leanh::LeanObject,
    mut v_i_1610_: *mut crate::leanh::LeanObject,
    mut v_entries_1611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1612_: usize = 0;
    let mut v_res_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1612_ = crate::leanh::lean_unbox_usize(v_depth_1607_);
    crate::leanh::lean_dec(v_depth_1607_);
    v_res_1613_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__8___redArg(v_depth_boxed_1612_, v_keys_1608_, v_vals_1609_, v_i_1610_, v_entries_1611_);
    crate::leanh::lean_dec_ref(v_vals_1609_);
    crate::leanh::lean_dec_ref(v_keys_1608_);
    return v_res_1613_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_x_1614_: *mut crate::leanh::LeanObject,
    mut v_x_1615_: *mut crate::leanh::LeanObject,
    mut v_x_1616_: *mut crate::leanh::LeanObject,
    mut v_x_1617_: *mut crate::leanh::LeanObject,
    mut v_x_1618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1621__boxed_1619_: usize = 0;
    let mut v_x_1622__boxed_1620_: usize = 0;
    let mut v_res_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1621__boxed_1619_ = crate::leanh::lean_unbox_usize(v_x_1615_);
    crate::leanh::lean_dec(v_x_1615_);
    v_x_1622__boxed_1620_ = crate::leanh::lean_unbox_usize(v_x_1616_);
    crate::leanh::lean_dec(v_x_1616_);
    v_res_1621_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg(v_x_1614_, v_x_1621__boxed_1619_, v_x_1622__boxed_1620_, v_x_1617_, v_x_1618_);
    return v_res_1621_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2___redArg(
    mut v_x_1622_: *mut crate::leanh::LeanObject,
    mut v_x_1623_: *mut crate::leanh::LeanObject,
    mut v_x_1624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1625_: u64 = 0;
    let mut v___x_1626_: usize = 0;
    let mut v___x_1627_: usize = 0;
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1625_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1623_);
    v___x_1626_ = lean_uint64_to_usize(v___x_1625_);
    v___x_1627_ = 1usize;
    v___x_1628_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg(v_x_1622_, v___x_1626_, v___x_1627_, v_x_1623_, v_x_1624_);
    return v___x_1628_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__0(
    mut v_x_1629_: *mut crate::leanh::LeanObject,
    mut v_keys_1630_: *mut crate::leanh::LeanObject,
    mut v_v_1631_: *mut crate::leanh::LeanObject,
    mut v_k_1632_: *mut crate::leanh::LeanObject,
    mut v_x_1633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1634_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1635_ = lean_nat_add(v_x_1629_, v___x_1634_);
    v_c_1636_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
        crate::leanh::lean_box(0),
        v_keys_1630_,
        v_v_1631_,
        v___x_1635_,
    );
    crate::leanh::lean_dec(v___x_1635_);
    v___x_1637_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1637_, 0, v_k_1632_);
    crate::leanh::lean_ctor_set(v___x_1637_, 1, v_c_1636_);
    return v___x_1637_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__0___boxed(
    mut v_x_1638_: *mut crate::leanh::LeanObject,
    mut v_keys_1639_: *mut crate::leanh::LeanObject,
    mut v_v_1640_: *mut crate::leanh::LeanObject,
    mut v_k_1641_: *mut crate::leanh::LeanObject,
    mut v_x_1642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1643_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__0(v_x_1638_, v_keys_1639_, v_v_1640_, v_k_1641_, v_x_1642_);
    crate::leanh::lean_dec_ref(v_keys_1639_);
    crate::leanh::lean_dec(v_x_1638_);
    return v_res_1643_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__1(
    mut v_a_1644_: *mut crate::leanh::LeanObject,
    mut v_b_1645_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: u8 = 0;
    v_fst_1646_ = crate::leanh::lean_ctor_get(v_a_1644_, 0);
    v_fst_1647_ = crate::leanh::lean_ctor_get(v_b_1645_, 0);
    v___x_1648_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1646_, v_fst_1647_);
    return v___x_1648_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__1___boxed(
    mut v_a_1649_: *mut crate::leanh::LeanObject,
    mut v_b_1650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1651_: u8 = 0;
    let mut v_r_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1651_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__1(v_a_1649_, v_b_1650_);
    crate::leanh::lean_dec_ref(v_b_1650_);
    crate::leanh::lean_dec_ref(v_a_1649_);
    v_r_1652_ = crate::leanh::lean_box((v_res_1651_) as usize);
    return v_r_1652_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__6_spec__11(
    mut v_vs_1653_: *mut crate::leanh::LeanObject,
    mut v_v_1654_: *mut crate::leanh::LeanObject,
    mut v_i_1655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: u8 = 0;
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: u8 = 0;
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1656_ = lean_array_get_size(v_vs_1653_);
                v___x_1657_ = lean_nat_dec_lt(v_i_1655_, v___x_1656_);
                if v___x_1657_ == 0 {
                    crate::leanh::lean_dec(v_i_1655_);
                    v___x_1658_ = lean_array_push(v_vs_1653_, v_v_1654_);
                    return v___x_1658_;
                } else {
                    v_proof_1659_ = crate::leanh::lean_ctor_get(v_v_1654_, 1);
                    v___x_1660_ = lean_array_fget_borrowed(v_vs_1653_, v_i_1655_);
                    v_proof_1661_ = crate::leanh::lean_ctor_get(v___x_1660_, 1);
                    crate::leanh::lean_inc_ref(v_proof_1661_);
                    crate::leanh::lean_inc_ref(v_proof_1659_);
                    v___x_1662_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(
                        v_proof_1659_,
                        v_proof_1661_,
                    );
                    if v___x_1662_ == 0 {
                        v___x_1663_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1664_ = lean_nat_add(v_i_1655_, v___x_1663_);
                        crate::leanh::lean_dec(v_i_1655_);
                        v_i_1655_ = v___x_1664_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1666_ = lean_array_fset(v_vs_1653_, v_i_1655_, v_v_1654_);
                        crate::leanh::lean_dec(v_i_1655_);
                        return v___x_1666_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__6(
    mut v_vs_1667_: *mut crate::leanh::LeanObject,
    mut v_v_1668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1669_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1670_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__6_spec__11(v_vs_1667_, v_v_1668_, v___x_1669_);
    return v___x_1670_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7_spec__13___redArg(
    mut v_x_1675_: *mut crate::leanh::LeanObject,
    mut v_keys_1676_: *mut crate::leanh::LeanObject,
    mut v_v_1677_: *mut crate::leanh::LeanObject,
    mut v_k_1678_: *mut crate::leanh::LeanObject,
    mut v_as_1679_: *mut crate::leanh::LeanObject,
    mut v_k_1680_: *mut crate::leanh::LeanObject,
    mut v_x_1681_: *mut crate::leanh::LeanObject,
    mut v_x_1682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_midVal_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: u8 = 0;
    let mut v___x_1688_: u8 = 0;
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: u8 = 0;
    let mut v_snd_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1694_: u8 = 0;
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1703_: u8 = 0;
    let mut v_unused_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: u8 = 0;
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_as_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1683_ = lean_nat_add(v_x_1681_, v_x_1682_);
                v___x_1684_ = crate::leanh::lean_unsigned_to_nat(1);
                v_mid_1685_ = lean_nat_shiftr(v___x_1683_, v___x_1684_);
                crate::leanh::lean_dec(v___x_1683_);
                v_midVal_1686_ = lean_array_fget(v_as_1679_, v_mid_1685_);
                v___x_1687_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__1(v_midVal_1686_, v_k_1680_);
                if v___x_1687_ == 0 {
                    crate::leanh::lean_dec(v_x_1682_);
                    v___x_1688_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__1(v_k_1680_, v_midVal_1686_);
                    if v___x_1688_ == 0 {
                        crate::leanh::lean_dec(v_x_1681_);
                        v___x_1689_ = lean_array_get_size(v_as_1679_);
                        v___x_1690_ = lean_nat_dec_lt(v_mid_1685_, v___x_1689_);
                        if v___x_1690_ == 0 {
                            crate::leanh::lean_dec(v_midVal_1686_);
                            crate::leanh::lean_dec(v_mid_1685_);
                            crate::leanh::lean_dec(v_k_1678_);
                            crate::leanh::lean_dec_ref(v_v_1677_);
                            return v_as_1679_;
                        } else {
                            v_snd_1691_ = crate::leanh::lean_ctor_get(v_midVal_1686_, 1);
                            v_isSharedCheck_1703_ =
                                (!crate::leanh::lean_is_exclusive(v_midVal_1686_)) as u8;
                            if v_isSharedCheck_1703_ == 0 {
                                v_unused_1704_ = crate::leanh::lean_ctor_get(v_midVal_1686_, 0);
                                crate::leanh::lean_dec(v_unused_1704_);
                                v___x_1693_ = v_midVal_1686_;
                                v_isShared_1694_ = v_isSharedCheck_1703_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_1691_);
                                crate::leanh::lean_dec(v_midVal_1686_);
                                v___x_1693_ = crate::leanh::lean_box(0);
                                v_isShared_1694_ = v_isSharedCheck_1703_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_midVal_1686_);
                        v_x_1682_ = v_mid_1685_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_midVal_1686_);
                    v___x_1706_ = lean_nat_dec_eq(v_mid_1685_, v_x_1681_);
                    if v___x_1706_ == 0 {
                        crate::leanh::lean_dec(v_x_1681_);
                        v_x_1681_ = v_mid_1685_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_mid_1685_);
                        crate::leanh::lean_dec(v_x_1682_);
                        v___x_1708_ = lean_nat_add(v_x_1675_, v___x_1684_);
                        v_c_1709_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(crate::leanh::lean_box(0), v_keys_1676_, v_v_1677_, v___x_1708_);
                        crate::leanh::lean_dec(v___x_1708_);
                        v___x_1710_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1710_, 0, v_k_1678_);
                        crate::leanh::lean_ctor_set(v___x_1710_, 1, v_c_1709_);
                        v___x_1711_ = lean_nat_add(v_x_1681_, v___x_1684_);
                        crate::leanh::lean_dec(v_x_1681_);
                        v_j_1712_ = lean_array_get_size(v_as_1679_);
                        v_as_1713_ = lean_array_push(v_as_1679_, v___x_1710_);
                        v___x_1714_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                            crate::leanh::lean_box(0),
                            v___x_1711_,
                            v_as_1713_,
                            v_j_1712_,
                        );
                        crate::leanh::lean_dec(v___x_1711_);
                        return v___x_1714_;
                    }
                }
            }
            1 => {
                v___x_1695_ = crate::leanh::lean_box(0);
                v_xs_x27_1696_ = lean_array_fset(v_as_1679_, v_mid_1685_, v___x_1695_);
                v___x_1697_ = lean_nat_add(v_x_1675_, v___x_1684_);
                v_c_1698_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3(v_keys_1676_, v_v_1677_, v___x_1697_, v_snd_1691_);
                crate::leanh::lean_dec(v___x_1697_);
                if v_isShared_1694_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1693_, 1, v_c_1698_);
                    crate::leanh::lean_ctor_set(v___x_1693_, 0, v_k_1678_);
                    v___x_1700_ = v___x_1693_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1702_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_k_1678_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_c_1698_);
                    v___x_1700_ = v_reuseFailAlloc_1702_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1701_ = lean_array_fset(v_xs_x27_1696_, v_mid_1685_, v___x_1700_);
                crate::leanh::lean_dec(v_mid_1685_);
                return v___x_1701_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7(
    mut v_x_1715_: *mut crate::leanh::LeanObject,
    mut v_keys_1716_: *mut crate::leanh::LeanObject,
    mut v_v_1717_: *mut crate::leanh::LeanObject,
    mut v_k_1718_: *mut crate::leanh::LeanObject,
    mut v_as_1719_: *mut crate::leanh::LeanObject,
    mut v_k_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: u8 = 0;
    v___x_1721_ = lean_array_get_size(v_as_1719_);
    v___x_1722_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1723_ = lean_nat_dec_eq(v___x_1721_, v___x_1722_);
    if v___x_1723_ == 0 {
        let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    crate::leanh::lean_dec(v_k_1718_);
                    crate::leanh::lean_dec_ref(v_v_1717_);
                    return v_as_1719_;
                } else {
                    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_xs_x27_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_inc(v___x_1724_);
                    v___x_1728_ = crate::leanh::lean_box(0);
                    v_xs_x27_1729_ = lean_array_fset(v_as_1719_, v___x_1722_, v___x_1728_);
                    v___x_1730_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__2(v_x_1715_, v_keys_1716_, v_v_1717_, v_k_1718_, v___x_1724_);
                    v___x_1731_ = lean_array_fset(v_xs_x27_1729_, v___x_1722_, v___x_1730_);
                    return v___x_1731_;
                }
            } else {
                let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1735_: u8 = 0;
                v___x_1732_ = crate::leanh::lean_unsigned_to_nat(1);
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
                            crate::leanh::lean_dec(v___x_1733_);
                            crate::leanh::lean_dec(v_k_1718_);
                            crate::leanh::lean_dec_ref(v_v_1717_);
                            return v_as_1719_;
                        } else {
                            let mut v___x_1738_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_xs_x27_1739_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1740_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1741_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_inc(v___x_1734_);
                            v___x_1738_ = crate::leanh::lean_box(0);
                            v_xs_x27_1739_ = lean_array_fset(v_as_1719_, v___x_1733_, v___x_1738_);
                            v___x_1740_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__2(v_x_1715_, v_keys_1716_, v_v_1717_, v_k_1718_, v___x_1734_);
                            v___x_1741_ = lean_array_fset(v_xs_x27_1739_, v___x_1733_, v___x_1740_);
                            crate::leanh::lean_dec(v___x_1733_);
                            return v___x_1741_;
                        }
                    } else {
                        let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_1742_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7_spec__13___redArg(v_x_1715_, v_keys_1716_, v_v_1717_, v_k_1718_, v_as_1719_, v_k_1720_, v___x_1722_, v___x_1733_);
                        return v___x_1742_;
                    }
                } else {
                    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_1733_);
                    v___x_1743_ = crate::leanh::lean_box(0);
                    v___x_1744_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__0(v_x_1715_, v_keys_1716_, v_v_1717_, v_k_1718_, v___x_1743_);
                    v___x_1745_ = lean_array_push(v_as_1719_, v___x_1744_);
                    return v___x_1745_;
                }
            }
        } else {
            let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_as_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1746_ = crate::leanh::lean_box(0);
            v___x_1747_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__0(v_x_1715_, v_keys_1716_, v_v_1717_, v_k_1718_, v___x_1746_);
            v_as_1748_ = lean_array_push(v_as_1719_, v___x_1747_);
            v___x_1749_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                crate::leanh::lean_box(0),
                v___x_1722_,
                v_as_1748_,
                v___x_1721_,
            );
            return v___x_1749_;
        }
    } else {
        let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1750_ = crate::leanh::lean_box(0);
        v___x_1751_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__0(v_x_1715_, v_keys_1716_, v_v_1717_, v_k_1718_, v___x_1750_);
        v___x_1752_ = lean_array_push(v_as_1719_, v___x_1751_);
        return v___x_1752_;
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3(
    mut v_keys_1753_: *mut crate::leanh::LeanObject,
    mut v_v_1754_: *mut crate::leanh::LeanObject,
    mut v_x_1755_: *mut crate::leanh::LeanObject,
    mut v_x_1756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vs_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1761_: u8 = 0;
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1775_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vs_1757_ = crate::leanh::lean_ctor_get(v_x_1756_, 0);
                v_children_1758_ = crate::leanh::lean_ctor_get(v_x_1756_, 1);
                v_isSharedCheck_1775_ = (!crate::leanh::lean_is_exclusive(v_x_1756_)) as u8;
                if v_isSharedCheck_1775_ == 0 {
                    v___x_1760_ = v_x_1756_;
                    v_isShared_1761_ = v_isSharedCheck_1775_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_children_1758_);
                    crate::leanh::lean_inc(v_vs_1757_);
                    crate::leanh::lean_dec(v_x_1756_);
                    v___x_1760_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_ctor_set(v___x_1760_, 0, v___x_1764_);
                        v___x_1766_ = v___x_1760_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1767_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_children_1758_);
                        v___x_1766_ = v_reuseFailAlloc_1767_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_1768_ = lean_array_fget_borrowed(v_keys_1753_, v_x_1755_);
                    v___x_1769_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3___closed__1;
                    crate::leanh::lean_inc_n(v_k_1768_, 2);
                    v___x_1770_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1770_, 0, v_k_1768_);
                    crate::leanh::lean_ctor_set(v___x_1770_, 1, v___x_1769_);
                    v_c_1771_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7(v_x_1755_, v_keys_1753_, v_v_1754_, v_k_1768_, v_children_1758_, v___x_1770_);
                    crate::leanh::lean_dec_ref_known(v___x_1770_, 2);
                    if v_isShared_1761_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1760_, 1, v_c_1771_);
                        v___x_1773_ = v___x_1760_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1774_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_vs_1757_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_c_1771_);
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
    mut v_x_1776_: *mut crate::leanh::LeanObject,
    mut v_keys_1777_: *mut crate::leanh::LeanObject,
    mut v_v_1778_: *mut crate::leanh::LeanObject,
    mut v_k_1779_: *mut crate::leanh::LeanObject,
    mut v_x_1780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1784_: u8 = 0;
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1791_: u8 = 0;
    let mut v_unused_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_1781_ = crate::leanh::lean_ctor_get(v_x_1780_, 1);
                v_isSharedCheck_1791_ = (!crate::leanh::lean_is_exclusive(v_x_1780_)) as u8;
                if v_isSharedCheck_1791_ == 0 {
                    v_unused_1792_ = crate::leanh::lean_ctor_get(v_x_1780_, 0);
                    crate::leanh::lean_dec(v_unused_1792_);
                    v___x_1783_ = v_x_1780_;
                    v_isShared_1784_ = v_isSharedCheck_1791_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1781_);
                    crate::leanh::lean_dec(v_x_1780_);
                    v___x_1783_ = crate::leanh::lean_box(0);
                    v_isShared_1784_ = v_isSharedCheck_1791_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1785_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1786_ = lean_nat_add(v_x_1776_, v___x_1785_);
                v_c_1787_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3(v_keys_1777_, v_v_1778_, v___x_1786_, v_snd_1781_);
                crate::leanh::lean_dec(v___x_1786_);
                if v_isShared_1784_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1783_, 1, v_c_1787_);
                    crate::leanh::lean_ctor_set(v___x_1783_, 0, v_k_1779_);
                    v___x_1789_ = v___x_1783_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1790_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_k_1779_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_c_1787_);
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
    mut v_x_1793_: *mut crate::leanh::LeanObject,
    mut v_keys_1794_: *mut crate::leanh::LeanObject,
    mut v_v_1795_: *mut crate::leanh::LeanObject,
    mut v_k_1796_: *mut crate::leanh::LeanObject,
    mut v_x_1797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1798_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___lam__2(v_x_1793_, v_keys_1794_, v_v_1795_, v_k_1796_, v_x_1797_);
    crate::leanh::lean_dec_ref(v_keys_1794_);
    crate::leanh::lean_dec(v_x_1793_);
    return v_res_1798_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3___boxed(
    mut v_keys_1799_: *mut crate::leanh::LeanObject,
    mut v_v_1800_: *mut crate::leanh::LeanObject,
    mut v_x_1801_: *mut crate::leanh::LeanObject,
    mut v_x_1802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1803_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3(v_keys_1799_, v_v_1800_, v_x_1801_, v_x_1802_);
    crate::leanh::lean_dec(v_x_1801_);
    crate::leanh::lean_dec_ref(v_keys_1799_);
    return v_res_1803_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7_spec__13___redArg___boxed(
    mut v_x_1804_: *mut crate::leanh::LeanObject,
    mut v_keys_1805_: *mut crate::leanh::LeanObject,
    mut v_v_1806_: *mut crate::leanh::LeanObject,
    mut v_k_1807_: *mut crate::leanh::LeanObject,
    mut v_as_1808_: *mut crate::leanh::LeanObject,
    mut v_k_1809_: *mut crate::leanh::LeanObject,
    mut v_x_1810_: *mut crate::leanh::LeanObject,
    mut v_x_1811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1812_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7_spec__13___redArg(v_x_1804_, v_keys_1805_, v_v_1806_, v_k_1807_, v_as_1808_, v_k_1809_, v_x_1810_, v_x_1811_);
    crate::leanh::lean_dec_ref(v_k_1809_);
    crate::leanh::lean_dec_ref(v_keys_1805_);
    crate::leanh::lean_dec(v_x_1804_);
    return v_res_1812_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7___boxed(
    mut v_x_1813_: *mut crate::leanh::LeanObject,
    mut v_keys_1814_: *mut crate::leanh::LeanObject,
    mut v_v_1815_: *mut crate::leanh::LeanObject,
    mut v_k_1816_: *mut crate::leanh::LeanObject,
    mut v_as_1817_: *mut crate::leanh::LeanObject,
    mut v_k_1818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1819_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7(v_x_1813_, v_keys_1814_, v_v_1815_, v_k_1816_, v_as_1817_, v_k_1818_);
    crate::leanh::lean_dec_ref(v_k_1818_);
    crate::leanh::lean_dec_ref(v_keys_1814_);
    crate::leanh::lean_dec(v_x_1813_);
    return v_res_1819_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__4___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1820_ = l_Lean_Meta_DiscrTree_instInhabited(crate::leanh::lean_box(0));
    return v___x_1820_;
}
pub unsafe fn l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__4(
    mut v_msg_1821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1822_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__4___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__4___closed__0_once), _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__4___closed__0);
    v___x_1823_ = lean_panic_fn_borrowed(v___x_1822_, v_msg_1821_);
    return v___x_1823_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_keys_1824_: *mut crate::leanh::LeanObject,
    mut v_vals_1825_: *mut crate::leanh::LeanObject,
    mut v_i_1826_: *mut crate::leanh::LeanObject,
    mut v_k_1827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: u8 = 0;
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: u8 = 0;
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1828_ = lean_array_get_size(v_keys_1824_);
                v___x_1829_ = lean_nat_dec_lt(v_i_1826_, v___x_1828_);
                if v___x_1829_ == 0 {
                    crate::leanh::lean_dec(v_i_1826_);
                    v___x_1830_ = crate::leanh::lean_box(0);
                    return v___x_1830_;
                } else {
                    v_k_x27_1831_ = lean_array_fget_borrowed(v_keys_1824_, v_i_1826_);
                    v___x_1832_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_1827_, v_k_x27_1831_);
                    if v___x_1832_ == 0 {
                        v___x_1833_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1834_ = lean_nat_add(v_i_1826_, v___x_1833_);
                        crate::leanh::lean_dec(v_i_1826_);
                        v_i_1826_ = v___x_1834_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1836_ = lean_array_fget_borrowed(v_vals_1825_, v_i_1826_);
                        crate::leanh::lean_dec(v_i_1826_);
                        crate::leanh::lean_inc(v___x_1836_);
                        v___x_1837_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1837_, 0, v___x_1836_);
                        return v___x_1837_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_keys_1838_: *mut crate::leanh::LeanObject,
    mut v_vals_1839_: *mut crate::leanh::LeanObject,
    mut v_i_1840_: *mut crate::leanh::LeanObject,
    mut v_k_1841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1842_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_keys_1838_, v_vals_1839_, v_i_1840_, v_k_1841_);
    crate::leanh::lean_dec(v_k_1841_);
    crate::leanh::lean_dec_ref(v_vals_1839_);
    crate::leanh::lean_dec_ref(v_keys_1838_);
    return v_res_1842_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_1843_: *mut crate::leanh::LeanObject,
    mut v_x_1844_: usize,
    mut v_x_1845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: usize = 0;
    let mut v___x_1849_: usize = 0;
    let mut v___x_1850_: usize = 0;
    let mut v_j_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: u8 = 0;
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: usize = 0;
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1843_) == 0 {
                    v_es_1846_ = crate::leanh::lean_ctor_get(v_x_1843_, 0);
                    v___x_1847_ = crate::leanh::lean_box(2);
                    v___x_1848_ = 5usize;
                    v___x_1849_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg___closed__1);
                    v___x_1850_ = lean_usize_land(v_x_1844_, v___x_1849_);
                    v_j_1851_ = lean_usize_to_nat(v___x_1850_);
                    v___x_1852_ = lean_array_get_borrowed(v___x_1847_, v_es_1846_, v_j_1851_);
                    crate::leanh::lean_dec(v_j_1851_);
                    match crate::leanh::lean_obj_tag(v___x_1852_) {
                        0 => {
                            v_key_1853_ = crate::leanh::lean_ctor_get(v___x_1852_, 0);
                            v_val_1854_ = crate::leanh::lean_ctor_get(v___x_1852_, 1);
                            v___x_1855_ =
                                l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1845_, v_key_1853_);
                            if v___x_1855_ == 0 {
                                v___x_1856_ = crate::leanh::lean_box(0);
                                return v___x_1856_;
                            } else {
                                crate::leanh::lean_inc(v_val_1854_);
                                v___x_1857_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1857_, 0, v_val_1854_);
                                return v___x_1857_;
                            }
                        }
                        1 => {
                            v_node_1858_ = crate::leanh::lean_ctor_get(v___x_1852_, 0);
                            v___x_1859_ = lean_usize_shift_right(v_x_1844_, v___x_1848_);
                            v_x_1843_ = v_node_1858_;
                            v_x_1844_ = v___x_1859_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1861_ = crate::leanh::lean_box(0);
                            return v___x_1861_;
                        }
                    }
                } else {
                    v_ks_1862_ = crate::leanh::lean_ctor_get(v_x_1843_, 0);
                    v_vs_1863_ = crate::leanh::lean_ctor_get(v_x_1843_, 1);
                    v___x_1864_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1865_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ks_1862_, v_vs_1863_, v___x_1864_, v_x_1845_);
                    return v___x_1865_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_x_1866_: *mut crate::leanh::LeanObject,
    mut v_x_1867_: *mut crate::leanh::LeanObject,
    mut v_x_1868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2068__boxed_1869_: usize = 0;
    let mut v_res_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2068__boxed_1869_ = crate::leanh::lean_unbox_usize(v_x_1867_);
    crate::leanh::lean_dec(v_x_1867_);
    v_res_1870_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1866_, v_x_2068__boxed_1869_, v_x_1868_);
    crate::leanh::lean_dec(v_x_1868_);
    crate::leanh::lean_dec_ref(v_x_1866_);
    return v_res_1870_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1___redArg(
    mut v_x_1871_: *mut crate::leanh::LeanObject,
    mut v_x_1872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1873_: u64 = 0;
    let mut v___x_1874_: usize = 0;
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1873_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1872_);
    v___x_1874_ = lean_uint64_to_usize(v___x_1873_);
    v___x_1875_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1871_, v___x_1874_, v_x_1872_);
    return v___x_1875_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_1876_: *mut crate::leanh::LeanObject,
    mut v_x_1877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1878_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1___redArg(v_x_1876_, v_x_1877_);
    crate::leanh::lean_dec(v_x_1877_);
    crate::leanh::lean_dec_ref(v_x_1876_);
    return v_res_1878_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1882_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__2;
    v___x_1883_ = crate::leanh::lean_unsigned_to_nat(23);
    v___x_1884_ = crate::leanh::lean_unsigned_to_nat(166);
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
    mut v_d_1888_: *mut crate::leanh::LeanObject,
    mut v_keys_1889_: *mut crate::leanh::LeanObject,
    mut v_v_1890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: u8 = 0;
    v___x_1891_ = lean_array_get_size(v_keys_1889_);
    v___x_1892_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1893_ = lean_nat_dec_eq(v___x_1891_, v___x_1892_);
    if v___x_1893_ == 0 {
        let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1894_ = crate::leanh::lean_box(0);
        v_k_1895_ = lean_array_get_borrowed(v___x_1894_, v_keys_1889_, v___x_1892_);
        v___x_1896_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1___redArg(v_d_1888_, v_k_1895_);
        if crate::leanh::lean_obj_tag(v___x_1896_) == 0 {
            let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1897_ = crate::leanh::lean_unsigned_to_nat(1);
            v_c_1898_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
                crate::leanh::lean_box(0),
                v_keys_1889_,
                v_v_1890_,
                v___x_1897_,
            );
            crate::leanh::lean_inc(v_k_1895_);
            v___x_1899_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2___redArg(v_d_1888_, v_k_1895_, v_c_1898_);
            return v___x_1899_;
        } else {
            let mut v_val_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_1900_ = crate::leanh::lean_ctor_get(v___x_1896_, 0);
            crate::leanh::lean_inc(v_val_1900_);
            crate::leanh::lean_dec_ref_known(v___x_1896_, 1);
            v___x_1901_ = crate::leanh::lean_unsigned_to_nat(1);
            v_c_1902_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3(v_keys_1889_, v_v_1890_, v___x_1901_, v_val_1900_);
            crate::leanh::lean_inc(v_k_1895_);
            v___x_1903_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2___redArg(v_d_1888_, v_k_1895_, v_c_1902_);
            return v___x_1903_;
        }
    } else {
        let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_v_1890_);
        crate::leanh::lean_dec_ref(v_d_1888_);
        v___x_1904_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__3_once), _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___closed__3);
        v___x_1905_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__4(v___x_1904_);
        return v___x_1905_;
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0___boxed(
    mut v_d_1906_: *mut crate::leanh::LeanObject,
    mut v_keys_1907_: *mut crate::leanh::LeanObject,
    mut v_v_1908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1909_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0(v_d_1906_, v_keys_1907_, v_v_1908_);
    crate::leanh::lean_dec_ref(v_keys_1907_);
    return v_res_1909_;
}
pub unsafe fn l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0(
    mut v_d_1910_: *mut crate::leanh::LeanObject,
    mut v_p_1911_: *mut crate::leanh::LeanObject,
    mut v_v_1912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keys_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keys_1913_ = l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(v_p_1911_);
    v___x_1914_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0(v_d_1910_, v_keys_1913_, v_v_1912_);
    crate::leanh::lean_dec_ref(v_keys_1913_);
    return v___x_1914_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec(
    mut v_s_1915_: *mut crate::leanh::LeanObject,
    mut v_thm_1916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_specs_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextDeclIdx_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v_specs_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1927_: u8 = 0;
    let mut v_pattern_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1936_: u8 = 0;
    let mut v_isSharedCheck_1937_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_specs_1917_ = crate::leanh::lean_ctor_get(v_s_1915_, 0);
                v_jps_1918_ = crate::leanh::lean_ctor_get(v_s_1915_, 1);
                v_nextDeclIdx_1919_ = crate::leanh::lean_ctor_get(v_s_1915_, 2);
                v_isSharedCheck_1937_ = (!crate::leanh::lean_is_exclusive(v_s_1915_)) as u8;
                if v_isSharedCheck_1937_ == 0 {
                    v___x_1921_ = v_s_1915_;
                    v_isShared_1922_ = v_isSharedCheck_1937_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nextDeclIdx_1919_);
                    crate::leanh::lean_inc(v_jps_1918_);
                    crate::leanh::lean_inc(v_specs_1917_);
                    crate::leanh::lean_dec(v_s_1915_);
                    v___x_1921_ = crate::leanh::lean_box(0);
                    v_isShared_1922_ = v_isSharedCheck_1937_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_specs_1923_ = crate::leanh::lean_ctor_get(v_specs_1917_, 0);
                v_erased_1924_ = crate::leanh::lean_ctor_get(v_specs_1917_, 1);
                v_isSharedCheck_1936_ = (!crate::leanh::lean_is_exclusive(v_specs_1917_)) as u8;
                if v_isSharedCheck_1936_ == 0 {
                    v___x_1926_ = v_specs_1917_;
                    v_isShared_1927_ = v_isSharedCheck_1936_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_erased_1924_);
                    crate::leanh::lean_inc(v_specs_1923_);
                    crate::leanh::lean_dec(v_specs_1917_);
                    v___x_1926_ = crate::leanh::lean_box(0);
                    v_isShared_1927_ = v_isSharedCheck_1936_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_pattern_1928_ = crate::leanh::lean_ctor_get(v_thm_1916_, 0);
                crate::leanh::lean_inc_ref(v_pattern_1928_);
                v___x_1929_ = l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0(v_specs_1923_, v_pattern_1928_, v_thm_1916_);
                if v_isShared_1927_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1926_, 0, v___x_1929_);
                    v___x_1931_ = v___x_1926_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1935_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1929_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_erased_1924_);
                    v___x_1931_ = v_reuseFailAlloc_1935_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1922_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1921_, 0, v___x_1931_);
                    v___x_1933_ = v___x_1921_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1934_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1931_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_jps_1918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1934_, 2, v_nextDeclIdx_1919_);
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
    mut v_00_u03b2_1938_: *mut crate::leanh::LeanObject,
    mut v_x_1939_: *mut crate::leanh::LeanObject,
    mut v_x_1940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1941_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1___redArg(v_x_1939_, v_x_1940_);
    return v___x_1941_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1942_: *mut crate::leanh::LeanObject,
    mut v_x_1943_: *mut crate::leanh::LeanObject,
    mut v_x_1944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1945_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1(v_00_u03b2_1942_, v_x_1943_, v_x_1944_);
    crate::leanh::lean_dec(v_x_1944_);
    crate::leanh::lean_dec_ref(v_x_1943_);
    return v_res_1945_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1946_: *mut crate::leanh::LeanObject,
    mut v_x_1947_: *mut crate::leanh::LeanObject,
    mut v_x_1948_: *mut crate::leanh::LeanObject,
    mut v_x_1949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1950_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2___redArg(v_x_1947_, v_x_1948_, v_x_1949_);
    return v___x_1950_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1951_: *mut crate::leanh::LeanObject,
    mut v_x_1952_: *mut crate::leanh::LeanObject,
    mut v_x_1953_: usize,
    mut v_x_1954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1955_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1952_, v_x_1953_, v_x_1954_);
    return v___x_1955_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b2_1956_: *mut crate::leanh::LeanObject,
    mut v_x_1957_: *mut crate::leanh::LeanObject,
    mut v_x_1958_: *mut crate::leanh::LeanObject,
    mut v_x_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2228__boxed_1960_: usize = 0;
    let mut v_res_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2228__boxed_1960_ = crate::leanh::lean_unbox_usize(v_x_1958_);
    crate::leanh::lean_dec(v_x_1958_);
    v_res_1961_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_1956_, v_x_1957_, v_x_2228__boxed_1960_, v_x_1959_);
    crate::leanh::lean_dec(v_x_1959_);
    crate::leanh::lean_dec_ref(v_x_1957_);
    return v_res_1961_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_1962_: *mut crate::leanh::LeanObject,
    mut v_x_1963_: *mut crate::leanh::LeanObject,
    mut v_x_1964_: usize,
    mut v_x_1965_: usize,
    mut v_x_1966_: *mut crate::leanh::LeanObject,
    mut v_x_1967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1968_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___redArg(v_x_1963_, v_x_1964_, v_x_1965_, v_x_1966_, v_x_1967_);
    return v___x_1968_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b2_1969_: *mut crate::leanh::LeanObject,
    mut v_x_1970_: *mut crate::leanh::LeanObject,
    mut v_x_1971_: *mut crate::leanh::LeanObject,
    mut v_x_1972_: *mut crate::leanh::LeanObject,
    mut v_x_1973_: *mut crate::leanh::LeanObject,
    mut v_x_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2239__boxed_1975_: usize = 0;
    let mut v_x_2240__boxed_1976_: usize = 0;
    let mut v_res_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2239__boxed_1975_ = crate::leanh::lean_unbox_usize(v_x_1971_);
    crate::leanh::lean_dec(v_x_1971_);
    v_x_2240__boxed_1976_ = crate::leanh::lean_unbox_usize(v_x_1972_);
    crate::leanh::lean_dec(v_x_1972_);
    v_res_1977_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_1969_, v_x_1970_, v_x_2239__boxed_1975_, v_x_2240__boxed_1976_, v_x_1973_, v_x_1974_);
    return v_res_1977_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_1978_: *mut crate::leanh::LeanObject,
    mut v_keys_1979_: *mut crate::leanh::LeanObject,
    mut v_vals_1980_: *mut crate::leanh::LeanObject,
    mut v_heq_1981_: *mut crate::leanh::LeanObject,
    mut v_i_1982_: *mut crate::leanh::LeanObject,
    mut v_k_1983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1984_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_keys_1979_, v_vals_1980_, v_i_1982_, v_k_1983_);
    return v___x_1984_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_1985_: *mut crate::leanh::LeanObject,
    mut v_keys_1986_: *mut crate::leanh::LeanObject,
    mut v_vals_1987_: *mut crate::leanh::LeanObject,
    mut v_heq_1988_: *mut crate::leanh::LeanObject,
    mut v_i_1989_: *mut crate::leanh::LeanObject,
    mut v_k_1990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1991_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b2_1985_, v_keys_1986_, v_vals_1987_, v_heq_1988_, v_i_1989_, v_k_1990_);
    crate::leanh::lean_dec(v_k_1990_);
    crate::leanh::lean_dec_ref(v_vals_1987_);
    crate::leanh::lean_dec_ref(v_keys_1986_);
    return v_res_1991_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__7(
    mut v_00_u03b2_1992_: *mut crate::leanh::LeanObject,
    mut v_n_1993_: *mut crate::leanh::LeanObject,
    mut v_k_1994_: *mut crate::leanh::LeanObject,
    mut v_v_1995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1996_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__7___redArg(v_n_1993_, v_k_1994_, v_v_1995_);
    return v___x_1996_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__8(
    mut v_00_u03b2_1997_: *mut crate::leanh::LeanObject,
    mut v_depth_1998_: usize,
    mut v_keys_1999_: *mut crate::leanh::LeanObject,
    mut v_vals_2000_: *mut crate::leanh::LeanObject,
    mut v_heq_2001_: *mut crate::leanh::LeanObject,
    mut v_i_2002_: *mut crate::leanh::LeanObject,
    mut v_entries_2003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2004_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__8___redArg(v_depth_1998_, v_keys_1999_, v_vals_2000_, v_i_2002_, v_entries_2003_);
    return v___x_2004_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__8___boxed(
    mut v_00_u03b2_2005_: *mut crate::leanh::LeanObject,
    mut v_depth_2006_: *mut crate::leanh::LeanObject,
    mut v_keys_2007_: *mut crate::leanh::LeanObject,
    mut v_vals_2008_: *mut crate::leanh::LeanObject,
    mut v_heq_2009_: *mut crate::leanh::LeanObject,
    mut v_i_2010_: *mut crate::leanh::LeanObject,
    mut v_entries_2011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2012_: usize = 0;
    let mut v_res_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2012_ = crate::leanh::lean_unbox_usize(v_depth_2006_);
    crate::leanh::lean_dec(v_depth_2006_);
    v_res_2013_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__8(v_00_u03b2_2005_, v_depth_boxed_2012_, v_keys_2007_, v_vals_2008_, v_heq_2009_, v_i_2010_, v_entries_2011_);
    crate::leanh::lean_dec_ref(v_vals_2008_);
    crate::leanh::lean_dec_ref(v_keys_2007_);
    return v_res_2013_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7_spec__13(
    mut v_x_2014_: *mut crate::leanh::LeanObject,
    mut v_keys_2015_: *mut crate::leanh::LeanObject,
    mut v_v_2016_: *mut crate::leanh::LeanObject,
    mut v_k_2017_: *mut crate::leanh::LeanObject,
    mut v_as_2018_: *mut crate::leanh::LeanObject,
    mut v_k_2019_: *mut crate::leanh::LeanObject,
    mut v_x_2020_: *mut crate::leanh::LeanObject,
    mut v_x_2021_: *mut crate::leanh::LeanObject,
    mut v_x_2022_: *mut crate::leanh::LeanObject,
    mut v_x_2023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2024_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7_spec__13___redArg(v_x_2014_, v_keys_2015_, v_v_2016_, v_k_2017_, v_as_2018_, v_k_2019_, v_x_2020_, v_x_2021_);
    return v___x_2024_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7_spec__13___boxed(
    mut v_x_2025_: *mut crate::leanh::LeanObject,
    mut v_keys_2026_: *mut crate::leanh::LeanObject,
    mut v_v_2027_: *mut crate::leanh::LeanObject,
    mut v_k_2028_: *mut crate::leanh::LeanObject,
    mut v_as_2029_: *mut crate::leanh::LeanObject,
    mut v_k_2030_: *mut crate::leanh::LeanObject,
    mut v_x_2031_: *mut crate::leanh::LeanObject,
    mut v_x_2032_: *mut crate::leanh::LeanObject,
    mut v_x_2033_: *mut crate::leanh::LeanObject,
    mut v_x_2034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2035_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__3_spec__7_spec__13(v_x_2025_, v_keys_2026_, v_v_2027_, v_k_2028_, v_as_2029_, v_k_2030_, v_x_2031_, v_x_2032_, v_x_2033_, v_x_2034_);
    crate::leanh::lean_dec_ref(v_k_2030_);
    crate::leanh::lean_dec_ref(v_keys_2026_);
    crate::leanh::lean_dec(v_x_2025_);
    return v_res_2035_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__7_spec__9(
    mut v_00_u03b2_2036_: *mut crate::leanh::LeanObject,
    mut v_x_2037_: *mut crate::leanh::LeanObject,
    mut v_x_2038_: *mut crate::leanh::LeanObject,
    mut v_x_2039_: *mut crate::leanh::LeanObject,
    mut v_x_2040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2041_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec_spec__0_spec__0_spec__2_spec__4_spec__7_spec__9___redArg(v_x_2037_, v_x_2038_, v_x_2039_, v_x_2040_);
    return v___x_2041_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(
    mut v_x_2042_: *mut crate::leanh::LeanObject,
    mut v___y_2043_: *mut crate::leanh::LeanObject,
    mut v___y_2044_: *mut crate::leanh::LeanObject,
    mut v___y_2045_: *mut crate::leanh::LeanObject,
    mut v___y_2046_: *mut crate::leanh::LeanObject,
    mut v___y_2047_: *mut crate::leanh::LeanObject,
    mut v___y_2048_: *mut crate::leanh::LeanObject,
    mut v___y_2049_: *mut crate::leanh::LeanObject,
    mut v___y_2050_: *mut crate::leanh::LeanObject,
    mut v___y_2051_: *mut crate::leanh::LeanObject,
    mut v___y_2052_: *mut crate::leanh::LeanObject,
    mut v___y_2053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2049_);
    crate::leanh::lean_inc_ref(v___y_2048_);
    crate::leanh::lean_inc(v___y_2047_);
    crate::leanh::lean_inc_ref(v___y_2046_);
    crate::leanh::lean_inc(v___y_2045_);
    crate::leanh::lean_inc(v___y_2044_);
    crate::leanh::lean_inc_ref(v___y_2043_);
    v___x_2055_ = crate::leanh::lean_apply_12(
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
        crate::leanh::lean_box(0),
    );
    return v___x_2055_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0___boxed(
    mut v_x_2056_: *mut crate::leanh::LeanObject,
    mut v___y_2057_: *mut crate::leanh::LeanObject,
    mut v___y_2058_: *mut crate::leanh::LeanObject,
    mut v___y_2059_: *mut crate::leanh::LeanObject,
    mut v___y_2060_: *mut crate::leanh::LeanObject,
    mut v___y_2061_: *mut crate::leanh::LeanObject,
    mut v___y_2062_: *mut crate::leanh::LeanObject,
    mut v___y_2063_: *mut crate::leanh::LeanObject,
    mut v___y_2064_: *mut crate::leanh::LeanObject,
    mut v___y_2065_: *mut crate::leanh::LeanObject,
    mut v___y_2066_: *mut crate::leanh::LeanObject,
    mut v___y_2067_: *mut crate::leanh::LeanObject,
    mut v___y_2068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2069_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(v_x_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
    crate::leanh::lean_dec(v___y_2063_);
    crate::leanh::lean_dec_ref(v___y_2062_);
    crate::leanh::lean_dec(v___y_2061_);
    crate::leanh::lean_dec_ref(v___y_2060_);
    crate::leanh::lean_dec(v___y_2059_);
    crate::leanh::lean_dec(v___y_2058_);
    crate::leanh::lean_dec_ref(v___y_2057_);
    return v_res_2069_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(
    mut v_mvarId_2070_: *mut crate::leanh::LeanObject,
    mut v_x_2071_: *mut crate::leanh::LeanObject,
    mut v___y_2072_: *mut crate::leanh::LeanObject,
    mut v___y_2073_: *mut crate::leanh::LeanObject,
    mut v___y_2074_: *mut crate::leanh::LeanObject,
    mut v___y_2075_: *mut crate::leanh::LeanObject,
    mut v___y_2076_: *mut crate::leanh::LeanObject,
    mut v___y_2077_: *mut crate::leanh::LeanObject,
    mut v___y_2078_: *mut crate::leanh::LeanObject,
    mut v___y_2079_: *mut crate::leanh::LeanObject,
    mut v___y_2080_: *mut crate::leanh::LeanObject,
    mut v___y_2081_: *mut crate::leanh::LeanObject,
    mut v___y_2082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2089_: u8 = 0;
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2093_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_2078_);
                crate::leanh::lean_inc_ref(v___y_2077_);
                crate::leanh::lean_inc(v___y_2076_);
                crate::leanh::lean_inc_ref(v___y_2075_);
                crate::leanh::lean_inc(v___y_2074_);
                crate::leanh::lean_inc(v___y_2073_);
                crate::leanh::lean_inc_ref(v___y_2072_);
                v___f_2084_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 8);
                crate::leanh::lean_closure_set(v___f_2084_, 0, v_x_2071_);
                crate::leanh::lean_closure_set(v___f_2084_, 1, v___y_2072_);
                crate::leanh::lean_closure_set(v___f_2084_, 2, v___y_2073_);
                crate::leanh::lean_closure_set(v___f_2084_, 3, v___y_2074_);
                crate::leanh::lean_closure_set(v___f_2084_, 4, v___y_2075_);
                crate::leanh::lean_closure_set(v___f_2084_, 5, v___y_2076_);
                crate::leanh::lean_closure_set(v___f_2084_, 6, v___y_2077_);
                crate::leanh::lean_closure_set(v___f_2084_, 7, v___y_2078_);
                v___x_2085_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_2070_,
                    v___f_2084_,
                    v___y_2079_,
                    v___y_2080_,
                    v___y_2081_,
                    v___y_2082_,
                );
                if crate::leanh::lean_obj_tag(v___x_2085_) == 0 {
                    return v___x_2085_;
                } else {
                    v_a_2086_ = crate::leanh::lean_ctor_get(v___x_2085_, 0);
                    v_isSharedCheck_2093_ = (!crate::leanh::lean_is_exclusive(v___x_2085_)) as u8;
                    if v_isSharedCheck_2093_ == 0 {
                        v___x_2088_ = v___x_2085_;
                        v_isShared_2089_ = v_isSharedCheck_2093_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2086_);
                        crate::leanh::lean_dec(v___x_2085_);
                        v___x_2088_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2092_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
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
    mut v_mvarId_2094_: *mut crate::leanh::LeanObject,
    mut v_x_2095_: *mut crate::leanh::LeanObject,
    mut v___y_2096_: *mut crate::leanh::LeanObject,
    mut v___y_2097_: *mut crate::leanh::LeanObject,
    mut v___y_2098_: *mut crate::leanh::LeanObject,
    mut v___y_2099_: *mut crate::leanh::LeanObject,
    mut v___y_2100_: *mut crate::leanh::LeanObject,
    mut v___y_2101_: *mut crate::leanh::LeanObject,
    mut v___y_2102_: *mut crate::leanh::LeanObject,
    mut v___y_2103_: *mut crate::leanh::LeanObject,
    mut v___y_2104_: *mut crate::leanh::LeanObject,
    mut v___y_2105_: *mut crate::leanh::LeanObject,
    mut v___y_2106_: *mut crate::leanh::LeanObject,
    mut v___y_2107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2108_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_mvarId_2094_, v_x_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
    crate::leanh::lean_dec(v___y_2106_);
    crate::leanh::lean_dec_ref(v___y_2105_);
    crate::leanh::lean_dec(v___y_2104_);
    crate::leanh::lean_dec_ref(v___y_2103_);
    crate::leanh::lean_dec(v___y_2102_);
    crate::leanh::lean_dec_ref(v___y_2101_);
    crate::leanh::lean_dec(v___y_2100_);
    crate::leanh::lean_dec_ref(v___y_2099_);
    crate::leanh::lean_dec(v___y_2098_);
    crate::leanh::lean_dec(v___y_2097_);
    crate::leanh::lean_dec_ref(v___y_2096_);
    return v_res_2108_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1(
    mut v_00_u03b1_2109_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2110_: *mut crate::leanh::LeanObject,
    mut v_x_2111_: *mut crate::leanh::LeanObject,
    mut v___y_2112_: *mut crate::leanh::LeanObject,
    mut v___y_2113_: *mut crate::leanh::LeanObject,
    mut v___y_2114_: *mut crate::leanh::LeanObject,
    mut v___y_2115_: *mut crate::leanh::LeanObject,
    mut v___y_2116_: *mut crate::leanh::LeanObject,
    mut v___y_2117_: *mut crate::leanh::LeanObject,
    mut v___y_2118_: *mut crate::leanh::LeanObject,
    mut v___y_2119_: *mut crate::leanh::LeanObject,
    mut v___y_2120_: *mut crate::leanh::LeanObject,
    mut v___y_2121_: *mut crate::leanh::LeanObject,
    mut v___y_2122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2124_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_mvarId_2110_, v_x_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
    return v___x_2124_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___boxed(
    mut v_00_u03b1_2125_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2126_: *mut crate::leanh::LeanObject,
    mut v_x_2127_: *mut crate::leanh::LeanObject,
    mut v___y_2128_: *mut crate::leanh::LeanObject,
    mut v___y_2129_: *mut crate::leanh::LeanObject,
    mut v___y_2130_: *mut crate::leanh::LeanObject,
    mut v___y_2131_: *mut crate::leanh::LeanObject,
    mut v___y_2132_: *mut crate::leanh::LeanObject,
    mut v___y_2133_: *mut crate::leanh::LeanObject,
    mut v___y_2134_: *mut crate::leanh::LeanObject,
    mut v___y_2135_: *mut crate::leanh::LeanObject,
    mut v___y_2136_: *mut crate::leanh::LeanObject,
    mut v___y_2137_: *mut crate::leanh::LeanObject,
    mut v___y_2138_: *mut crate::leanh::LeanObject,
    mut v___y_2139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2140_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1(v_00_u03b1_2125_, v_mvarId_2126_, v_x_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
    crate::leanh::lean_dec(v___y_2138_);
    crate::leanh::lean_dec_ref(v___y_2137_);
    crate::leanh::lean_dec(v___y_2136_);
    crate::leanh::lean_dec_ref(v___y_2135_);
    crate::leanh::lean_dec(v___y_2134_);
    crate::leanh::lean_dec_ref(v___y_2133_);
    crate::leanh::lean_dec(v___y_2132_);
    crate::leanh::lean_dec_ref(v___y_2131_);
    crate::leanh::lean_dec(v___y_2130_);
    crate::leanh::lean_dec(v___y_2129_);
    crate::leanh::lean_dec_ref(v___y_2128_);
    return v_res_2140_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(
    mut v_as_2141_: *mut crate::leanh::LeanObject,
    mut v_i_2142_: usize,
    mut v_stop_2143_: usize,
    mut v_b_2144_: *mut crate::leanh::LeanObject,
    mut v___y_2145_: *mut crate::leanh::LeanObject,
    mut v___y_2146_: *mut crate::leanh::LeanObject,
    mut v___y_2147_: *mut crate::leanh::LeanObject,
    mut v___y_2148_: *mut crate::leanh::LeanObject,
    mut v___y_2149_: *mut crate::leanh::LeanObject,
    mut v___y_2150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: usize = 0;
    let mut v___x_2155_: usize = 0;
    let mut v___x_2157_: u8 = 0;
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2162_: u8 = 0;
    let mut v___x_2163_: u8 = 0;
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2175_: u8 = 0;
    let mut v___y_2177_: u8 = 0;
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: u8 = 0;
    let mut v___x_2182_: u8 = 0;
    let mut v_isSharedCheck_2183_: u8 = 0;
    let mut v_reuseFailAlloc_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2185_: u8 = 0;
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2157_ = lean_usize_dec_eq(v_i_2142_, v_stop_2143_);
                if v___x_2157_ == 0 {
                    v___x_2158_ = lean_array_uget(v_as_2141_, v_i_2142_);
                    if crate::leanh::lean_obj_tag(v___x_2158_) == 0 {
                        v_a_2153_ = v_b_2144_;
                        state = 1;
                        continue;
                    } else {
                        v_val_2159_ = crate::leanh::lean_ctor_get(v___x_2158_, 0);
                        v_isSharedCheck_2185_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2158_)) as u8;
                        if v_isSharedCheck_2185_ == 0 {
                            v___x_2161_ = v___x_2158_;
                            v_isShared_2162_ = v_isSharedCheck_2185_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2159_);
                            crate::leanh::lean_dec(v___x_2158_);
                            v___x_2161_ = crate::leanh::lean_box(0);
                            v_isShared_2162_ = v_isSharedCheck_2185_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_2186_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2186_, 0, v_b_2144_);
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
                    crate::leanh::lean_dec(v_val_2159_);
                    if v_isShared_2162_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2161_, 0, v___x_2164_);
                        v___x_2166_ = v___x_2161_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2184_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2164_);
                        v___x_2166_ = v_reuseFailAlloc_2184_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2161_);
                    crate::leanh::lean_dec(v_val_2159_);
                    v_a_2153_ = v_b_2144_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2167_ = crate::leanh::lean_unsigned_to_nat(100);
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
                if crate::leanh::lean_obj_tag(v___x_2168_) == 0 {
                    v_a_2169_ = crate::leanh::lean_ctor_get(v___x_2168_, 0);
                    crate::leanh::lean_inc(v_a_2169_);
                    crate::leanh::lean_dec_ref_known(v___x_2168_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2169_) == 1 {
                        v_val_2170_ = crate::leanh::lean_ctor_get(v_a_2169_, 0);
                        crate::leanh::lean_inc(v_val_2170_);
                        crate::leanh::lean_dec_ref_known(v_a_2169_, 1);
                        v___x_2171_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec(
                            v_b_2144_,
                            v_val_2170_,
                        );
                        v_a_2153_ = v___x_2171_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_2169_);
                        v_a_2153_ = v_b_2144_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2172_ = crate::leanh::lean_ctor_get(v___x_2168_, 0);
                    v_isSharedCheck_2183_ = (!crate::leanh::lean_is_exclusive(v___x_2168_)) as u8;
                    if v_isSharedCheck_2183_ == 0 {
                        v___x_2174_ = v___x_2168_;
                        v_isShared_2175_ = v_isSharedCheck_2183_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2172_);
                        crate::leanh::lean_dec(v___x_2168_);
                        v___x_2174_ = crate::leanh::lean_box(0);
                        v_isShared_2175_ = v_isSharedCheck_2183_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2181_ = l_Lean_Exception_isInterrupt(v_a_2172_);
                if v___x_2181_ == 0 {
                    crate::leanh::lean_inc(v_a_2172_);
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
                    crate::leanh::lean_del_object(v___x_2174_);
                    crate::leanh::lean_dec(v_a_2172_);
                    v_a_2153_ = v_b_2144_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_b_2144_);
                    if v_isShared_2175_ == 0 {
                        v___x_2179_ = v___x_2174_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2180_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2172_);
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
    mut v_as_2187_: *mut crate::leanh::LeanObject,
    mut v_i_2188_: *mut crate::leanh::LeanObject,
    mut v_stop_2189_: *mut crate::leanh::LeanObject,
    mut v_b_2190_: *mut crate::leanh::LeanObject,
    mut v___y_2191_: *mut crate::leanh::LeanObject,
    mut v___y_2192_: *mut crate::leanh::LeanObject,
    mut v___y_2193_: *mut crate::leanh::LeanObject,
    mut v___y_2194_: *mut crate::leanh::LeanObject,
    mut v___y_2195_: *mut crate::leanh::LeanObject,
    mut v___y_2196_: *mut crate::leanh::LeanObject,
    mut v___y_2197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2198_: usize = 0;
    let mut v_stop_boxed_2199_: usize = 0;
    let mut v_res_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2198_ = crate::leanh::lean_unbox_usize(v_i_2188_);
    crate::leanh::lean_dec(v_i_2188_);
    v_stop_boxed_2199_ = crate::leanh::lean_unbox_usize(v_stop_2189_);
    crate::leanh::lean_dec(v_stop_2189_);
    v_res_2200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_as_2187_, v_i_boxed_2198_, v_stop_boxed_2199_, v_b_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
    crate::leanh::lean_dec(v___y_2196_);
    crate::leanh::lean_dec_ref(v___y_2195_);
    crate::leanh::lean_dec(v___y_2194_);
    crate::leanh::lean_dec_ref(v___y_2193_);
    crate::leanh::lean_dec(v___y_2192_);
    crate::leanh::lean_dec_ref(v___y_2191_);
    crate::leanh::lean_dec_ref(v_as_2187_);
    return v_res_2200_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(
    mut v_x_2201_: *mut crate::leanh::LeanObject,
    mut v_x_2202_: *mut crate::leanh::LeanObject,
    mut v___y_2203_: *mut crate::leanh::LeanObject,
    mut v___y_2204_: *mut crate::leanh::LeanObject,
    mut v___y_2205_: *mut crate::leanh::LeanObject,
    mut v___y_2206_: *mut crate::leanh::LeanObject,
    mut v___y_2207_: *mut crate::leanh::LeanObject,
    mut v___y_2208_: *mut crate::leanh::LeanObject,
    mut v___y_2209_: *mut crate::leanh::LeanObject,
    mut v___y_2210_: *mut crate::leanh::LeanObject,
    mut v___y_2211_: *mut crate::leanh::LeanObject,
    mut v___y_2212_: *mut crate::leanh::LeanObject,
    mut v___y_2213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2218_: u8 = 0;
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: u8 = 0;
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: usize = 0;
    let mut v___x_2230_: usize = 0;
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: usize = 0;
    let mut v___x_2233_: usize = 0;
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2235_: u8 = 0;
    let mut v_vs_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2239_: u8 = 0;
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: u8 = 0;
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: u8 = 0;
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: usize = 0;
    let mut v___x_2251_: usize = 0;
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: usize = 0;
    let mut v___x_2254_: usize = 0;
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2256_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2201_) == 0 {
                    v_cs_2215_ = crate::leanh::lean_ctor_get(v_x_2201_, 0);
                    v_isSharedCheck_2235_ = (!crate::leanh::lean_is_exclusive(v_x_2201_)) as u8;
                    if v_isSharedCheck_2235_ == 0 {
                        v___x_2217_ = v_x_2201_;
                        v_isShared_2218_ = v_isSharedCheck_2235_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cs_2215_);
                        crate::leanh::lean_dec(v_x_2201_);
                        v___x_2217_ = crate::leanh::lean_box(0);
                        v_isShared_2218_ = v_isSharedCheck_2235_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_2236_ = crate::leanh::lean_ctor_get(v_x_2201_, 0);
                    v_isSharedCheck_2256_ = (!crate::leanh::lean_is_exclusive(v_x_2201_)) as u8;
                    if v_isSharedCheck_2256_ == 0 {
                        v___x_2238_ = v_x_2201_;
                        v_isShared_2239_ = v_isSharedCheck_2256_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2236_);
                        crate::leanh::lean_dec(v_x_2201_);
                        v___x_2238_ = crate::leanh::lean_box(0);
                        v_isShared_2239_ = v_isSharedCheck_2256_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2219_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2220_ = lean_array_get_size(v_cs_2215_);
                v___x_2221_ = lean_nat_dec_lt(v___x_2219_, v___x_2220_);
                if v___x_2221_ == 0 {
                    crate::leanh::lean_dec_ref(v_cs_2215_);
                    if v_isShared_2218_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2217_, 0, v_x_2202_);
                        v___x_2223_ = v___x_2217_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2224_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_x_2202_);
                        v___x_2223_ = v_reuseFailAlloc_2224_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2225_ = lean_nat_dec_le(v___x_2220_, v___x_2220_);
                    if v___x_2225_ == 0 {
                        if v___x_2221_ == 0 {
                            crate::leanh::lean_dec_ref(v_cs_2215_);
                            if v_isShared_2218_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2217_, 0, v_x_2202_);
                                v___x_2227_ = v___x_2217_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2228_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_x_2202_);
                                v___x_2227_ = v_reuseFailAlloc_2228_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2217_);
                            v___x_2229_ = 0usize;
                            v___x_2230_ = lean_usize_of_nat(v___x_2220_);
                            v___x_2231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_2215_, v___x_2229_, v___x_2230_, v_x_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
                            crate::leanh::lean_dec_ref(v_cs_2215_);
                            return v___x_2231_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2217_);
                        v___x_2232_ = 0usize;
                        v___x_2233_ = lean_usize_of_nat(v___x_2220_);
                        v___x_2234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_2215_, v___x_2232_, v___x_2233_, v_x_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
                        crate::leanh::lean_dec_ref(v_cs_2215_);
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
                v___x_2240_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2241_ = lean_array_get_size(v_vs_2236_);
                v___x_2242_ = lean_nat_dec_lt(v___x_2240_, v___x_2241_);
                if v___x_2242_ == 0 {
                    crate::leanh::lean_dec_ref(v_vs_2236_);
                    if v_isShared_2239_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2238_, 0);
                        crate::leanh::lean_ctor_set(v___x_2238_, 0, v_x_2202_);
                        v___x_2244_ = v___x_2238_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2245_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_x_2202_);
                        v___x_2244_ = v_reuseFailAlloc_2245_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_2246_ = lean_nat_dec_le(v___x_2241_, v___x_2241_);
                    if v___x_2246_ == 0 {
                        if v___x_2242_ == 0 {
                            crate::leanh::lean_dec_ref(v_vs_2236_);
                            if v_isShared_2239_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_2238_, 0);
                                crate::leanh::lean_ctor_set(v___x_2238_, 0, v_x_2202_);
                                v___x_2248_ = v___x_2238_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_2249_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_x_2202_);
                                v___x_2248_ = v_reuseFailAlloc_2249_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2238_);
                            v___x_2250_ = 0usize;
                            v___x_2251_ = lean_usize_of_nat(v___x_2241_);
                            v___x_2252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_2236_, v___x_2250_, v___x_2251_, v_x_2202_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
                            crate::leanh::lean_dec_ref(v_vs_2236_);
                            return v___x_2252_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2238_);
                        v___x_2253_ = 0usize;
                        v___x_2254_ = lean_usize_of_nat(v___x_2241_);
                        v___x_2255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_2236_, v___x_2253_, v___x_2254_, v_x_2202_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
                        crate::leanh::lean_dec_ref(v_vs_2236_);
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
    mut v_as_2257_: *mut crate::leanh::LeanObject,
    mut v_i_2258_: usize,
    mut v_stop_2259_: usize,
    mut v_b_2260_: *mut crate::leanh::LeanObject,
    mut v___y_2261_: *mut crate::leanh::LeanObject,
    mut v___y_2262_: *mut crate::leanh::LeanObject,
    mut v___y_2263_: *mut crate::leanh::LeanObject,
    mut v___y_2264_: *mut crate::leanh::LeanObject,
    mut v___y_2265_: *mut crate::leanh::LeanObject,
    mut v___y_2266_: *mut crate::leanh::LeanObject,
    mut v___y_2267_: *mut crate::leanh::LeanObject,
    mut v___y_2268_: *mut crate::leanh::LeanObject,
    mut v___y_2269_: *mut crate::leanh::LeanObject,
    mut v___y_2270_: *mut crate::leanh::LeanObject,
    mut v___y_2271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2273_: u8 = 0;
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: usize = 0;
    let mut v___x_2278_: usize = 0;
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2273_ = lean_usize_dec_eq(v_i_2258_, v_stop_2259_);
                if v___x_2273_ == 0 {
                    v___x_2274_ = lean_array_uget_borrowed(v_as_2257_, v_i_2258_);
                    crate::leanh::lean_inc(v___x_2274_);
                    v___x_2275_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v___x_2274_, v_b_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
                    if crate::leanh::lean_obj_tag(v___x_2275_) == 0 {
                        v_a_2276_ = crate::leanh::lean_ctor_get(v___x_2275_, 0);
                        crate::leanh::lean_inc(v_a_2276_);
                        crate::leanh::lean_dec_ref_known(v___x_2275_, 1);
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
                    v___x_2280_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2280_, 0, v_b_2260_);
                    return v___x_2280_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_as_2281_: *mut crate::leanh::LeanObject,
    mut v_i_2282_: *mut crate::leanh::LeanObject,
    mut v_stop_2283_: *mut crate::leanh::LeanObject,
    mut v_b_2284_: *mut crate::leanh::LeanObject,
    mut v___y_2285_: *mut crate::leanh::LeanObject,
    mut v___y_2286_: *mut crate::leanh::LeanObject,
    mut v___y_2287_: *mut crate::leanh::LeanObject,
    mut v___y_2288_: *mut crate::leanh::LeanObject,
    mut v___y_2289_: *mut crate::leanh::LeanObject,
    mut v___y_2290_: *mut crate::leanh::LeanObject,
    mut v___y_2291_: *mut crate::leanh::LeanObject,
    mut v___y_2292_: *mut crate::leanh::LeanObject,
    mut v___y_2293_: *mut crate::leanh::LeanObject,
    mut v___y_2294_: *mut crate::leanh::LeanObject,
    mut v___y_2295_: *mut crate::leanh::LeanObject,
    mut v___y_2296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2297_: usize = 0;
    let mut v_stop_boxed_2298_: usize = 0;
    let mut v_res_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2297_ = crate::leanh::lean_unbox_usize(v_i_2282_);
    crate::leanh::lean_dec(v_i_2282_);
    v_stop_boxed_2298_ = crate::leanh::lean_unbox_usize(v_stop_2283_);
    crate::leanh::lean_dec(v_stop_2283_);
    v_res_2299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_as_2281_, v_i_boxed_2297_, v_stop_boxed_2298_, v_b_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
    crate::leanh::lean_dec(v___y_2295_);
    crate::leanh::lean_dec_ref(v___y_2294_);
    crate::leanh::lean_dec(v___y_2293_);
    crate::leanh::lean_dec_ref(v___y_2292_);
    crate::leanh::lean_dec(v___y_2291_);
    crate::leanh::lean_dec_ref(v___y_2290_);
    crate::leanh::lean_dec(v___y_2289_);
    crate::leanh::lean_dec_ref(v___y_2288_);
    crate::leanh::lean_dec(v___y_2287_);
    crate::leanh::lean_dec(v___y_2286_);
    crate::leanh::lean_dec_ref(v___y_2285_);
    crate::leanh::lean_dec_ref(v_as_2281_);
    return v_res_2299_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4___boxed(
    mut v_x_2300_: *mut crate::leanh::LeanObject,
    mut v_x_2301_: *mut crate::leanh::LeanObject,
    mut v___y_2302_: *mut crate::leanh::LeanObject,
    mut v___y_2303_: *mut crate::leanh::LeanObject,
    mut v___y_2304_: *mut crate::leanh::LeanObject,
    mut v___y_2305_: *mut crate::leanh::LeanObject,
    mut v___y_2306_: *mut crate::leanh::LeanObject,
    mut v___y_2307_: *mut crate::leanh::LeanObject,
    mut v___y_2308_: *mut crate::leanh::LeanObject,
    mut v___y_2309_: *mut crate::leanh::LeanObject,
    mut v___y_2310_: *mut crate::leanh::LeanObject,
    mut v___y_2311_: *mut crate::leanh::LeanObject,
    mut v___y_2312_: *mut crate::leanh::LeanObject,
    mut v___y_2313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2314_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v_x_2300_, v_x_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
    crate::leanh::lean_dec(v___y_2312_);
    crate::leanh::lean_dec_ref(v___y_2311_);
    crate::leanh::lean_dec(v___y_2310_);
    crate::leanh::lean_dec_ref(v___y_2309_);
    crate::leanh::lean_dec(v___y_2308_);
    crate::leanh::lean_dec_ref(v___y_2307_);
    crate::leanh::lean_dec(v___y_2306_);
    crate::leanh::lean_dec_ref(v___y_2305_);
    crate::leanh::lean_dec(v___y_2304_);
    crate::leanh::lean_dec(v___y_2303_);
    crate::leanh::lean_dec_ref(v___y_2302_);
    return v_res_2314_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2315_ = l_Lean_instInhabitedPersistentArrayNode_default(crate::leanh::lean_box(0));
    return v___x_2315_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(
    mut v_x_2316_: *mut crate::leanh::LeanObject,
    mut v_x_2317_: usize,
    mut v_x_2318_: usize,
    mut v_x_2319_: *mut crate::leanh::LeanObject,
    mut v___y_2320_: *mut crate::leanh::LeanObject,
    mut v___y_2321_: *mut crate::leanh::LeanObject,
    mut v___y_2322_: *mut crate::leanh::LeanObject,
    mut v___y_2323_: *mut crate::leanh::LeanObject,
    mut v___y_2324_: *mut crate::leanh::LeanObject,
    mut v___y_2325_: *mut crate::leanh::LeanObject,
    mut v___y_2326_: *mut crate::leanh::LeanObject,
    mut v___y_2327_: *mut crate::leanh::LeanObject,
    mut v___y_2328_: *mut crate::leanh::LeanObject,
    mut v___y_2329_: *mut crate::leanh::LeanObject,
    mut v___y_2330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: usize = 0;
    let mut v_j_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: usize = 0;
    let mut v___x_2338_: usize = 0;
    let mut v___x_2339_: usize = 0;
    let mut v___x_2340_: usize = 0;
    let mut v___x_2341_: usize = 0;
    let mut v___x_2342_: usize = 0;
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: u8 = 0;
    let mut v___x_2349_: u8 = 0;
    let mut v___x_2350_: usize = 0;
    let mut v___x_2351_: usize = 0;
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: usize = 0;
    let mut v___x_2354_: usize = 0;
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2359_: u8 = 0;
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: u8 = 0;
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: u8 = 0;
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: usize = 0;
    let mut v___x_2371_: usize = 0;
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: usize = 0;
    let mut v___x_2374_: usize = 0;
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2376_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2316_) == 0 {
                    v_cs_2332_ = crate::leanh::lean_ctor_get(v_x_2316_, 0);
                    crate::leanh::lean_inc_ref(v_cs_2332_);
                    crate::leanh::lean_dec_ref_known(v_x_2316_, 1);
                    v___x_2333_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0);
                    v___x_2334_ = lean_usize_shift_right(v_x_2317_, v_x_2318_);
                    v_j_2335_ = lean_usize_to_nat(v___x_2334_);
                    v___x_2336_ = lean_array_get_borrowed(v___x_2333_, v_cs_2332_, v_j_2335_);
                    v___x_2337_ = 1usize;
                    v___x_2338_ = lean_usize_shift_left(v___x_2337_, v_x_2318_);
                    v___x_2339_ = lean_usize_sub(v___x_2338_, v___x_2337_);
                    v___x_2340_ = lean_usize_land(v_x_2317_, v___x_2339_);
                    v___x_2341_ = 5usize;
                    v___x_2342_ = lean_usize_sub(v_x_2318_, v___x_2341_);
                    crate::leanh::lean_inc(v___x_2336_);
                    v___x_2343_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v___x_2336_, v___x_2340_, v___x_2342_, v_x_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
                    if crate::leanh::lean_obj_tag(v___x_2343_) == 0 {
                        v_a_2344_ = crate::leanh::lean_ctor_get(v___x_2343_, 0);
                        crate::leanh::lean_inc(v_a_2344_);
                        v___x_2345_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2346_ = lean_nat_add(v_j_2335_, v___x_2345_);
                        crate::leanh::lean_dec(v_j_2335_);
                        v___x_2347_ = lean_array_get_size(v_cs_2332_);
                        v___x_2348_ = lean_nat_dec_lt(v___x_2346_, v___x_2347_);
                        if v___x_2348_ == 0 {
                            crate::leanh::lean_dec(v___x_2346_);
                            crate::leanh::lean_dec(v_a_2344_);
                            crate::leanh::lean_dec_ref(v_cs_2332_);
                            return v___x_2343_;
                        } else {
                            v___x_2349_ = lean_nat_dec_le(v___x_2347_, v___x_2347_);
                            if v___x_2349_ == 0 {
                                if v___x_2348_ == 0 {
                                    crate::leanh::lean_dec(v___x_2346_);
                                    crate::leanh::lean_dec(v_a_2344_);
                                    crate::leanh::lean_dec_ref(v_cs_2332_);
                                    return v___x_2343_;
                                } else {
                                    crate::leanh::lean_dec_ref_known(v___x_2343_, 1);
                                    v___x_2350_ = lean_usize_of_nat(v___x_2346_);
                                    crate::leanh::lean_dec(v___x_2346_);
                                    v___x_2351_ = lean_usize_of_nat(v___x_2347_);
                                    v___x_2352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_2332_, v___x_2350_, v___x_2351_, v_a_2344_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
                                    crate::leanh::lean_dec_ref(v_cs_2332_);
                                    return v___x_2352_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_2343_, 1);
                                v___x_2353_ = lean_usize_of_nat(v___x_2346_);
                                crate::leanh::lean_dec(v___x_2346_);
                                v___x_2354_ = lean_usize_of_nat(v___x_2347_);
                                v___x_2355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_2332_, v___x_2353_, v___x_2354_, v_a_2344_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
                                crate::leanh::lean_dec_ref(v_cs_2332_);
                                return v___x_2355_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_j_2335_);
                        crate::leanh::lean_dec_ref(v_cs_2332_);
                        return v___x_2343_;
                    }
                } else {
                    v_vs_2356_ = crate::leanh::lean_ctor_get(v_x_2316_, 0);
                    v_isSharedCheck_2376_ = (!crate::leanh::lean_is_exclusive(v_x_2316_)) as u8;
                    if v_isSharedCheck_2376_ == 0 {
                        v___x_2358_ = v_x_2316_;
                        v_isShared_2359_ = v_isSharedCheck_2376_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2356_);
                        crate::leanh::lean_dec(v_x_2316_);
                        v___x_2358_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_dec(v___x_2360_);
                    crate::leanh::lean_dec_ref(v_vs_2356_);
                    if v_isShared_2359_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2358_, 0);
                        crate::leanh::lean_ctor_set(v___x_2358_, 0, v_x_2319_);
                        v___x_2364_ = v___x_2358_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2365_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_x_2319_);
                        v___x_2364_ = v_reuseFailAlloc_2365_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2366_ = lean_nat_dec_le(v___x_2361_, v___x_2361_);
                    if v___x_2366_ == 0 {
                        if v___x_2362_ == 0 {
                            crate::leanh::lean_dec(v___x_2360_);
                            crate::leanh::lean_dec_ref(v_vs_2356_);
                            if v_isShared_2359_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_2358_, 0);
                                crate::leanh::lean_ctor_set(v___x_2358_, 0, v_x_2319_);
                                v___x_2368_ = v___x_2358_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2369_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_x_2319_);
                                v___x_2368_ = v_reuseFailAlloc_2369_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2358_);
                            v___x_2370_ = lean_usize_of_nat(v___x_2360_);
                            crate::leanh::lean_dec(v___x_2360_);
                            v___x_2371_ = lean_usize_of_nat(v___x_2361_);
                            v___x_2372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_2356_, v___x_2370_, v___x_2371_, v_x_2319_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
                            crate::leanh::lean_dec_ref(v_vs_2356_);
                            return v___x_2372_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2358_);
                        v___x_2373_ = lean_usize_of_nat(v___x_2360_);
                        crate::leanh::lean_dec(v___x_2360_);
                        v___x_2374_ = lean_usize_of_nat(v___x_2361_);
                        v___x_2375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_2356_, v___x_2373_, v___x_2374_, v_x_2319_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
                        crate::leanh::lean_dec_ref(v_vs_2356_);
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
    mut v_x_2377_: *mut crate::leanh::LeanObject,
    mut v_x_2378_: *mut crate::leanh::LeanObject,
    mut v_x_2379_: *mut crate::leanh::LeanObject,
    mut v_x_2380_: *mut crate::leanh::LeanObject,
    mut v___y_2381_: *mut crate::leanh::LeanObject,
    mut v___y_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
    mut v___y_2385_: *mut crate::leanh::LeanObject,
    mut v___y_2386_: *mut crate::leanh::LeanObject,
    mut v___y_2387_: *mut crate::leanh::LeanObject,
    mut v___y_2388_: *mut crate::leanh::LeanObject,
    mut v___y_2389_: *mut crate::leanh::LeanObject,
    mut v___y_2390_: *mut crate::leanh::LeanObject,
    mut v___y_2391_: *mut crate::leanh::LeanObject,
    mut v___y_2392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_24362__boxed_2393_: usize = 0;
    let mut v_x_24363__boxed_2394_: usize = 0;
    let mut v_res_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_24362__boxed_2393_ = crate::leanh::lean_unbox_usize(v_x_2378_);
    crate::leanh::lean_dec(v_x_2378_);
    v_x_24363__boxed_2394_ = crate::leanh::lean_unbox_usize(v_x_2379_);
    crate::leanh::lean_dec(v_x_2379_);
    v_res_2395_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v_x_2377_, v_x_24362__boxed_2393_, v_x_24363__boxed_2394_, v_x_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
    crate::leanh::lean_dec(v___y_2391_);
    crate::leanh::lean_dec_ref(v___y_2390_);
    crate::leanh::lean_dec(v___y_2389_);
    crate::leanh::lean_dec_ref(v___y_2388_);
    crate::leanh::lean_dec(v___y_2387_);
    crate::leanh::lean_dec_ref(v___y_2386_);
    crate::leanh::lean_dec(v___y_2385_);
    crate::leanh::lean_dec_ref(v___y_2384_);
    crate::leanh::lean_dec(v___y_2383_);
    crate::leanh::lean_dec(v___y_2382_);
    crate::leanh::lean_dec_ref(v___y_2381_);
    return v_res_2395_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(
    mut v_t_2396_: *mut crate::leanh::LeanObject,
    mut v_init_2397_: *mut crate::leanh::LeanObject,
    mut v_start_2398_: *mut crate::leanh::LeanObject,
    mut v___y_2399_: *mut crate::leanh::LeanObject,
    mut v___y_2400_: *mut crate::leanh::LeanObject,
    mut v___y_2401_: *mut crate::leanh::LeanObject,
    mut v___y_2402_: *mut crate::leanh::LeanObject,
    mut v___y_2403_: *mut crate::leanh::LeanObject,
    mut v___y_2404_: *mut crate::leanh::LeanObject,
    mut v___y_2405_: *mut crate::leanh::LeanObject,
    mut v___y_2406_: *mut crate::leanh::LeanObject,
    mut v___y_2407_: *mut crate::leanh::LeanObject,
    mut v___y_2408_: *mut crate::leanh::LeanObject,
    mut v___y_2409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: u8 = 0;
    v___x_2411_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2412_ = lean_nat_dec_eq(v_start_2398_, v___x_2411_);
    if v___x_2412_ == 0 {
        let mut v_root_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_shift_2415_: usize = 0;
        let mut v_tailOff_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2417_: u8 = 0;
        v_root_2413_ = crate::leanh::lean_ctor_get(v_t_2396_, 0);
        crate::leanh::lean_inc_ref(v_root_2413_);
        v_tail_2414_ = crate::leanh::lean_ctor_get(v_t_2396_, 1);
        crate::leanh::lean_inc_ref(v_tail_2414_);
        v_shift_2415_ = crate::leanh::lean_ctor_get_usize(v_t_2396_, 4);
        v_tailOff_2416_ = crate::leanh::lean_ctor_get(v_t_2396_, 3);
        crate::leanh::lean_inc(v_tailOff_2416_);
        crate::leanh::lean_dec_ref(v_t_2396_);
        v___x_2417_ = lean_nat_dec_le(v_tailOff_2416_, v_start_2398_);
        if v___x_2417_ == 0 {
            let mut v___x_2418_: usize = 0;
            let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_tailOff_2416_);
            v___x_2418_ = lean_usize_of_nat(v_start_2398_);
            v___x_2419_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v_root_2413_, v___x_2418_, v_shift_2415_, v_init_2397_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
            if crate::leanh::lean_obj_tag(v___x_2419_) == 0 {
                let mut v_a_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2422_: u8 = 0;
                v_a_2420_ = crate::leanh::lean_ctor_get(v___x_2419_, 0);
                crate::leanh::lean_inc(v_a_2420_);
                v___x_2421_ = lean_array_get_size(v_tail_2414_);
                v___x_2422_ = lean_nat_dec_lt(v___x_2411_, v___x_2421_);
                if v___x_2422_ == 0 {
                    crate::leanh::lean_dec(v_a_2420_);
                    crate::leanh::lean_dec_ref(v_tail_2414_);
                    return v___x_2419_;
                } else {
                    let mut v___x_2423_: u8 = 0;
                    v___x_2423_ = lean_nat_dec_le(v___x_2421_, v___x_2421_);
                    if v___x_2423_ == 0 {
                        if v___x_2422_ == 0 {
                            crate::leanh::lean_dec(v_a_2420_);
                            crate::leanh::lean_dec_ref(v_tail_2414_);
                            return v___x_2419_;
                        } else {
                            let mut v___x_2424_: usize = 0;
                            let mut v___x_2425_: usize = 0;
                            let mut v___x_2426_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec_ref_known(v___x_2419_, 1);
                            v___x_2424_ = 0usize;
                            v___x_2425_ = lean_usize_of_nat(v___x_2421_);
                            v___x_2426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_2414_, v___x_2424_, v___x_2425_, v_a_2420_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
                            crate::leanh::lean_dec_ref(v_tail_2414_);
                            return v___x_2426_;
                        }
                    } else {
                        let mut v___x_2427_: usize = 0;
                        let mut v___x_2428_: usize = 0;
                        let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec_ref_known(v___x_2419_, 1);
                        v___x_2427_ = 0usize;
                        v___x_2428_ = lean_usize_of_nat(v___x_2421_);
                        v___x_2429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_2414_, v___x_2427_, v___x_2428_, v_a_2420_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
                        crate::leanh::lean_dec_ref(v_tail_2414_);
                        return v___x_2429_;
                    }
                }
            } else {
                crate::leanh::lean_dec_ref(v_tail_2414_);
                return v___x_2419_;
            }
        } else {
            let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2432_: u8 = 0;
            crate::leanh::lean_dec_ref(v_root_2413_);
            v___x_2430_ = lean_nat_sub(v_start_2398_, v_tailOff_2416_);
            crate::leanh::lean_dec(v_tailOff_2416_);
            v___x_2431_ = lean_array_get_size(v_tail_2414_);
            v___x_2432_ = lean_nat_dec_lt(v___x_2430_, v___x_2431_);
            if v___x_2432_ == 0 {
                let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_2430_);
                crate::leanh::lean_dec_ref(v_tail_2414_);
                v___x_2433_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2433_, 0, v_init_2397_);
                return v___x_2433_;
            } else {
                let mut v___x_2434_: u8 = 0;
                v___x_2434_ = lean_nat_dec_le(v___x_2431_, v___x_2431_);
                if v___x_2434_ == 0 {
                    if v___x_2432_ == 0 {
                        let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v___x_2430_);
                        crate::leanh::lean_dec_ref(v_tail_2414_);
                        v___x_2435_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2435_, 0, v_init_2397_);
                        return v___x_2435_;
                    } else {
                        let mut v___x_2436_: usize = 0;
                        let mut v___x_2437_: usize = 0;
                        let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_2436_ = lean_usize_of_nat(v___x_2430_);
                        crate::leanh::lean_dec(v___x_2430_);
                        v___x_2437_ = lean_usize_of_nat(v___x_2431_);
                        v___x_2438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_2414_, v___x_2436_, v___x_2437_, v_init_2397_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
                        crate::leanh::lean_dec_ref(v_tail_2414_);
                        return v___x_2438_;
                    }
                } else {
                    let mut v___x_2439_: usize = 0;
                    let mut v___x_2440_: usize = 0;
                    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_2439_ = lean_usize_of_nat(v___x_2430_);
                    crate::leanh::lean_dec(v___x_2430_);
                    v___x_2440_ = lean_usize_of_nat(v___x_2431_);
                    v___x_2441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_2414_, v___x_2439_, v___x_2440_, v_init_2397_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
                    crate::leanh::lean_dec_ref(v_tail_2414_);
                    return v___x_2441_;
                }
            }
        }
    } else {
        let mut v_root_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_root_2442_ = crate::leanh::lean_ctor_get(v_t_2396_, 0);
        crate::leanh::lean_inc_ref(v_root_2442_);
        v_tail_2443_ = crate::leanh::lean_ctor_get(v_t_2396_, 1);
        crate::leanh::lean_inc_ref(v_tail_2443_);
        crate::leanh::lean_dec_ref(v_t_2396_);
        v___x_2444_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v_root_2442_, v_init_2397_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
        if crate::leanh::lean_obj_tag(v___x_2444_) == 0 {
            let mut v_a_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2447_: u8 = 0;
            v_a_2445_ = crate::leanh::lean_ctor_get(v___x_2444_, 0);
            crate::leanh::lean_inc(v_a_2445_);
            v___x_2446_ = lean_array_get_size(v_tail_2443_);
            v___x_2447_ = lean_nat_dec_lt(v___x_2411_, v___x_2446_);
            if v___x_2447_ == 0 {
                crate::leanh::lean_dec(v_a_2445_);
                crate::leanh::lean_dec_ref(v_tail_2443_);
                return v___x_2444_;
            } else {
                let mut v___x_2448_: u8 = 0;
                v___x_2448_ = lean_nat_dec_le(v___x_2446_, v___x_2446_);
                if v___x_2448_ == 0 {
                    if v___x_2447_ == 0 {
                        crate::leanh::lean_dec(v_a_2445_);
                        crate::leanh::lean_dec_ref(v_tail_2443_);
                        return v___x_2444_;
                    } else {
                        let mut v___x_2449_: usize = 0;
                        let mut v___x_2450_: usize = 0;
                        let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec_ref_known(v___x_2444_, 1);
                        v___x_2449_ = 0usize;
                        v___x_2450_ = lean_usize_of_nat(v___x_2446_);
                        v___x_2451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_2443_, v___x_2449_, v___x_2450_, v_a_2445_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
                        crate::leanh::lean_dec_ref(v_tail_2443_);
                        return v___x_2451_;
                    }
                } else {
                    let mut v___x_2452_: usize = 0;
                    let mut v___x_2453_: usize = 0;
                    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref_known(v___x_2444_, 1);
                    v___x_2452_ = 0usize;
                    v___x_2453_ = lean_usize_of_nat(v___x_2446_);
                    v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_2443_, v___x_2452_, v___x_2453_, v_a_2445_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
                    crate::leanh::lean_dec_ref(v_tail_2443_);
                    return v___x_2454_;
                }
            }
        } else {
            crate::leanh::lean_dec_ref(v_tail_2443_);
            return v___x_2444_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0___boxed(
    mut v_t_2455_: *mut crate::leanh::LeanObject,
    mut v_init_2456_: *mut crate::leanh::LeanObject,
    mut v_start_2457_: *mut crate::leanh::LeanObject,
    mut v___y_2458_: *mut crate::leanh::LeanObject,
    mut v___y_2459_: *mut crate::leanh::LeanObject,
    mut v___y_2460_: *mut crate::leanh::LeanObject,
    mut v___y_2461_: *mut crate::leanh::LeanObject,
    mut v___y_2462_: *mut crate::leanh::LeanObject,
    mut v___y_2463_: *mut crate::leanh::LeanObject,
    mut v___y_2464_: *mut crate::leanh::LeanObject,
    mut v___y_2465_: *mut crate::leanh::LeanObject,
    mut v___y_2466_: *mut crate::leanh::LeanObject,
    mut v___y_2467_: *mut crate::leanh::LeanObject,
    mut v___y_2468_: *mut crate::leanh::LeanObject,
    mut v___y_2469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2470_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(v_t_2455_, v_init_2456_, v_start_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
    crate::leanh::lean_dec(v___y_2468_);
    crate::leanh::lean_dec_ref(v___y_2467_);
    crate::leanh::lean_dec(v___y_2466_);
    crate::leanh::lean_dec_ref(v___y_2465_);
    crate::leanh::lean_dec(v___y_2464_);
    crate::leanh::lean_dec_ref(v___y_2463_);
    crate::leanh::lean_dec(v___y_2462_);
    crate::leanh::lean_dec_ref(v___y_2461_);
    crate::leanh::lean_dec(v___y_2460_);
    crate::leanh::lean_dec(v___y_2459_);
    crate::leanh::lean_dec_ref(v___y_2458_);
    crate::leanh::lean_dec(v_start_2457_);
    return v_res_2470_;
}
pub unsafe fn l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0(
    mut v_lctx_2471_: *mut crate::leanh::LeanObject,
    mut v_init_2472_: *mut crate::leanh::LeanObject,
    mut v_start_2473_: *mut crate::leanh::LeanObject,
    mut v___y_2474_: *mut crate::leanh::LeanObject,
    mut v___y_2475_: *mut crate::leanh::LeanObject,
    mut v___y_2476_: *mut crate::leanh::LeanObject,
    mut v___y_2477_: *mut crate::leanh::LeanObject,
    mut v___y_2478_: *mut crate::leanh::LeanObject,
    mut v___y_2479_: *mut crate::leanh::LeanObject,
    mut v___y_2480_: *mut crate::leanh::LeanObject,
    mut v___y_2481_: *mut crate::leanh::LeanObject,
    mut v___y_2482_: *mut crate::leanh::LeanObject,
    mut v___y_2483_: *mut crate::leanh::LeanObject,
    mut v___y_2484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decls_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_decls_2486_ = crate::leanh::lean_ctor_get(v_lctx_2471_, 1);
    crate::leanh::lean_inc_ref(v_decls_2486_);
    crate::leanh::lean_dec_ref(v_lctx_2471_);
    v___x_2487_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(v_decls_2486_, v_init_2472_, v_start_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
    return v___x_2487_;
}
pub unsafe fn l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0___boxed(
    mut v_lctx_2488_: *mut crate::leanh::LeanObject,
    mut v_init_2489_: *mut crate::leanh::LeanObject,
    mut v_start_2490_: *mut crate::leanh::LeanObject,
    mut v___y_2491_: *mut crate::leanh::LeanObject,
    mut v___y_2492_: *mut crate::leanh::LeanObject,
    mut v___y_2493_: *mut crate::leanh::LeanObject,
    mut v___y_2494_: *mut crate::leanh::LeanObject,
    mut v___y_2495_: *mut crate::leanh::LeanObject,
    mut v___y_2496_: *mut crate::leanh::LeanObject,
    mut v___y_2497_: *mut crate::leanh::LeanObject,
    mut v___y_2498_: *mut crate::leanh::LeanObject,
    mut v___y_2499_: *mut crate::leanh::LeanObject,
    mut v___y_2500_: *mut crate::leanh::LeanObject,
    mut v___y_2501_: *mut crate::leanh::LeanObject,
    mut v___y_2502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2503_ = l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0(v_lctx_2488_, v_init_2489_, v_start_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
    crate::leanh::lean_dec(v___y_2501_);
    crate::leanh::lean_dec_ref(v___y_2500_);
    crate::leanh::lean_dec(v___y_2499_);
    crate::leanh::lean_dec_ref(v___y_2498_);
    crate::leanh::lean_dec(v___y_2497_);
    crate::leanh::lean_dec_ref(v___y_2496_);
    crate::leanh::lean_dec(v___y_2495_);
    crate::leanh::lean_dec_ref(v___y_2494_);
    crate::leanh::lean_dec(v___y_2493_);
    crate::leanh::lean_dec(v___y_2492_);
    crate::leanh::lean_dec_ref(v___y_2491_);
    crate::leanh::lean_dec(v_start_2490_);
    return v_res_2503_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___lam__0(
    mut v_scope_2504_: *mut crate::leanh::LeanObject,
    mut v___y_2505_: *mut crate::leanh::LeanObject,
    mut v___y_2506_: *mut crate::leanh::LeanObject,
    mut v___y_2507_: *mut crate::leanh::LeanObject,
    mut v___y_2508_: *mut crate::leanh::LeanObject,
    mut v___y_2509_: *mut crate::leanh::LeanObject,
    mut v___y_2510_: *mut crate::leanh::LeanObject,
    mut v___y_2511_: *mut crate::leanh::LeanObject,
    mut v___y_2512_: *mut crate::leanh::LeanObject,
    mut v___y_2513_: *mut crate::leanh::LeanObject,
    mut v___y_2514_: *mut crate::leanh::LeanObject,
    mut v___y_2515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextDeclIdx_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: u8 = 0;
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2526_: u8 = 0;
    let mut v_specs_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jps_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2531_: u8 = 0;
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2538_: u8 = 0;
    let mut v_unused_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2540_: u8 = 0;
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_2517_ = crate::leanh::lean_ctor_get(v___y_2512_, 2);
                v_decls_2518_ = crate::leanh::lean_ctor_get(v_lctx_2517_, 1);
                v_nextDeclIdx_2519_ = crate::leanh::lean_ctor_get(v_scope_2504_, 2);
                v_size_2520_ = crate::leanh::lean_ctor_get(v_decls_2518_, 2);
                v___x_2521_ = lean_nat_dec_eq(v_nextDeclIdx_2519_, v_size_2520_);
                if v___x_2521_ == 0 {
                    crate::leanh::lean_inc(v_nextDeclIdx_2519_);
                    crate::leanh::lean_inc_ref(v_lctx_2517_);
                    v___x_2522_ = l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0(v_lctx_2517_, v_scope_2504_, v_nextDeclIdx_2519_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
                    crate::leanh::lean_dec(v_nextDeclIdx_2519_);
                    if crate::leanh::lean_obj_tag(v___x_2522_) == 0 {
                        v_a_2523_ = crate::leanh::lean_ctor_get(v___x_2522_, 0);
                        v_isSharedCheck_2540_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2522_)) as u8;
                        if v_isSharedCheck_2540_ == 0 {
                            v___x_2525_ = v___x_2522_;
                            v_isShared_2526_ = v_isSharedCheck_2540_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2523_);
                            crate::leanh::lean_dec(v___x_2522_);
                            v___x_2525_ = crate::leanh::lean_box(0);
                            v_isShared_2526_ = v_isSharedCheck_2540_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_2522_;
                    }
                } else {
                    v___x_2541_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2541_, 0, v_scope_2504_);
                    return v___x_2541_;
                }
            }
            1 => {
                v_specs_2527_ = crate::leanh::lean_ctor_get(v_a_2523_, 0);
                v_jps_2528_ = crate::leanh::lean_ctor_get(v_a_2523_, 1);
                v_isSharedCheck_2538_ = (!crate::leanh::lean_is_exclusive(v_a_2523_)) as u8;
                if v_isSharedCheck_2538_ == 0 {
                    v_unused_2539_ = crate::leanh::lean_ctor_get(v_a_2523_, 2);
                    crate::leanh::lean_dec(v_unused_2539_);
                    v___x_2530_ = v_a_2523_;
                    v_isShared_2531_ = v_isSharedCheck_2538_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_jps_2528_);
                    crate::leanh::lean_inc(v_specs_2527_);
                    crate::leanh::lean_dec(v_a_2523_);
                    v___x_2530_ = crate::leanh::lean_box(0);
                    v_isShared_2531_ = v_isSharedCheck_2538_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_size_2520_);
                if v_isShared_2531_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2530_, 2, v_size_2520_);
                    v___x_2533_ = v___x_2530_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2537_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_specs_2527_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_jps_2528_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 2, v_size_2520_);
                    v___x_2533_ = v_reuseFailAlloc_2537_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2526_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2525_, 0, v___x_2533_);
                    v___x_2535_ = v___x_2525_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2536_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2533_);
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
    mut v_scope_2542_: *mut crate::leanh::LeanObject,
    mut v___y_2543_: *mut crate::leanh::LeanObject,
    mut v___y_2544_: *mut crate::leanh::LeanObject,
    mut v___y_2545_: *mut crate::leanh::LeanObject,
    mut v___y_2546_: *mut crate::leanh::LeanObject,
    mut v___y_2547_: *mut crate::leanh::LeanObject,
    mut v___y_2548_: *mut crate::leanh::LeanObject,
    mut v___y_2549_: *mut crate::leanh::LeanObject,
    mut v___y_2550_: *mut crate::leanh::LeanObject,
    mut v___y_2551_: *mut crate::leanh::LeanObject,
    mut v___y_2552_: *mut crate::leanh::LeanObject,
    mut v___y_2553_: *mut crate::leanh::LeanObject,
    mut v___y_2554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_2553_);
    crate::leanh::lean_dec_ref(v___y_2552_);
    crate::leanh::lean_dec(v___y_2551_);
    crate::leanh::lean_dec_ref(v___y_2550_);
    crate::leanh::lean_dec(v___y_2549_);
    crate::leanh::lean_dec_ref(v___y_2548_);
    crate::leanh::lean_dec(v___y_2547_);
    crate::leanh::lean_dec_ref(v___y_2546_);
    crate::leanh::lean_dec(v___y_2545_);
    crate::leanh::lean_dec(v___y_2544_);
    crate::leanh::lean_dec_ref(v___y_2543_);
    return v_res_2555_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs(
    mut v_scope_2556_: *mut crate::leanh::LeanObject,
    mut v_goal_2557_: *mut crate::leanh::LeanObject,
    mut v_a_2558_: *mut crate::leanh::LeanObject,
    mut v_a_2559_: *mut crate::leanh::LeanObject,
    mut v_a_2560_: *mut crate::leanh::LeanObject,
    mut v_a_2561_: *mut crate::leanh::LeanObject,
    mut v_a_2562_: *mut crate::leanh::LeanObject,
    mut v_a_2563_: *mut crate::leanh::LeanObject,
    mut v_a_2564_: *mut crate::leanh::LeanObject,
    mut v_a_2565_: *mut crate::leanh::LeanObject,
    mut v_a_2566_: *mut crate::leanh::LeanObject,
    mut v_a_2567_: *mut crate::leanh::LeanObject,
    mut v_a_2568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2570_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___lam__0___boxed
            as *mut core::ffi::c_void,
        13,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2570_, 0, v_scope_2556_);
    v___x_2571_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_goal_2557_, v___f_2570_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
    return v___x_2571_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___boxed(
    mut v_scope_2572_: *mut crate::leanh::LeanObject,
    mut v_goal_2573_: *mut crate::leanh::LeanObject,
    mut v_a_2574_: *mut crate::leanh::LeanObject,
    mut v_a_2575_: *mut crate::leanh::LeanObject,
    mut v_a_2576_: *mut crate::leanh::LeanObject,
    mut v_a_2577_: *mut crate::leanh::LeanObject,
    mut v_a_2578_: *mut crate::leanh::LeanObject,
    mut v_a_2579_: *mut crate::leanh::LeanObject,
    mut v_a_2580_: *mut crate::leanh::LeanObject,
    mut v_a_2581_: *mut crate::leanh::LeanObject,
    mut v_a_2582_: *mut crate::leanh::LeanObject,
    mut v_a_2583_: *mut crate::leanh::LeanObject,
    mut v_a_2584_: *mut crate::leanh::LeanObject,
    mut v_a_2585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_2584_);
    crate::leanh::lean_dec_ref(v_a_2583_);
    crate::leanh::lean_dec(v_a_2582_);
    crate::leanh::lean_dec_ref(v_a_2581_);
    crate::leanh::lean_dec(v_a_2580_);
    crate::leanh::lean_dec_ref(v_a_2579_);
    crate::leanh::lean_dec(v_a_2578_);
    crate::leanh::lean_dec_ref(v_a_2577_);
    crate::leanh::lean_dec(v_a_2576_);
    crate::leanh::lean_dec(v_a_2575_);
    crate::leanh::lean_dec_ref(v_a_2574_);
    return v_res_2586_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(
    mut v_as_2587_: *mut crate::leanh::LeanObject,
    mut v_i_2588_: usize,
    mut v_stop_2589_: usize,
    mut v_b_2590_: *mut crate::leanh::LeanObject,
    mut v___y_2591_: *mut crate::leanh::LeanObject,
    mut v___y_2592_: *mut crate::leanh::LeanObject,
    mut v___y_2593_: *mut crate::leanh::LeanObject,
    mut v___y_2594_: *mut crate::leanh::LeanObject,
    mut v___y_2595_: *mut crate::leanh::LeanObject,
    mut v___y_2596_: *mut crate::leanh::LeanObject,
    mut v___y_2597_: *mut crate::leanh::LeanObject,
    mut v___y_2598_: *mut crate::leanh::LeanObject,
    mut v___y_2599_: *mut crate::leanh::LeanObject,
    mut v___y_2600_: *mut crate::leanh::LeanObject,
    mut v___y_2601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_as_2587_, v_i_2588_, v_stop_2589_, v_b_2590_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
    return v___x_2603_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___boxed(
    mut v_as_2604_: *mut crate::leanh::LeanObject,
    mut v_i_2605_: *mut crate::leanh::LeanObject,
    mut v_stop_2606_: *mut crate::leanh::LeanObject,
    mut v_b_2607_: *mut crate::leanh::LeanObject,
    mut v___y_2608_: *mut crate::leanh::LeanObject,
    mut v___y_2609_: *mut crate::leanh::LeanObject,
    mut v___y_2610_: *mut crate::leanh::LeanObject,
    mut v___y_2611_: *mut crate::leanh::LeanObject,
    mut v___y_2612_: *mut crate::leanh::LeanObject,
    mut v___y_2613_: *mut crate::leanh::LeanObject,
    mut v___y_2614_: *mut crate::leanh::LeanObject,
    mut v___y_2615_: *mut crate::leanh::LeanObject,
    mut v___y_2616_: *mut crate::leanh::LeanObject,
    mut v___y_2617_: *mut crate::leanh::LeanObject,
    mut v___y_2618_: *mut crate::leanh::LeanObject,
    mut v___y_2619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2620_: usize = 0;
    let mut v_stop_boxed_2621_: usize = 0;
    let mut v_res_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2620_ = crate::leanh::lean_unbox_usize(v_i_2605_);
    crate::leanh::lean_dec(v_i_2605_);
    v_stop_boxed_2621_ = crate::leanh::lean_unbox_usize(v_stop_2606_);
    crate::leanh::lean_dec(v_stop_2606_);
    v_res_2622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(v_as_2604_, v_i_boxed_2620_, v_stop_boxed_2621_, v_b_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
    crate::leanh::lean_dec(v___y_2618_);
    crate::leanh::lean_dec_ref(v___y_2617_);
    crate::leanh::lean_dec(v___y_2616_);
    crate::leanh::lean_dec_ref(v___y_2615_);
    crate::leanh::lean_dec(v___y_2614_);
    crate::leanh::lean_dec_ref(v___y_2613_);
    crate::leanh::lean_dec(v___y_2612_);
    crate::leanh::lean_dec_ref(v___y_2611_);
    crate::leanh::lean_dec(v___y_2610_);
    crate::leanh::lean_dec(v___y_2609_);
    crate::leanh::lean_dec_ref(v___y_2608_);
    crate::leanh::lean_dec_ref(v_as_2604_);
    return v_res_2622_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(
    mut v_a_2623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fuel_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2630_: u8 = 0;
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: u8 = 0;
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2637_: u8 = 0;
    let mut v___x_2638_: u8 = 0;
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2625_ = lean_st_ref_get(v_a_2623_);
                v_fuel_2626_ = crate::leanh::lean_ctor_get(v___x_2625_, 5);
                crate::leanh::lean_inc(v_fuel_2626_);
                crate::leanh::lean_dec(v___x_2625_);
                if crate::leanh::lean_obj_tag(v_fuel_2626_) == 0 {
                    v_n_2627_ = crate::leanh::lean_ctor_get(v_fuel_2626_, 0);
                    v_isSharedCheck_2637_ = (!crate::leanh::lean_is_exclusive(v_fuel_2626_)) as u8;
                    if v_isSharedCheck_2637_ == 0 {
                        v___x_2629_ = v_fuel_2626_;
                        v_isShared_2630_ = v_isSharedCheck_2637_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_n_2627_);
                        crate::leanh::lean_dec(v_fuel_2626_);
                        v___x_2629_ = crate::leanh::lean_box(0);
                        v_isShared_2630_ = v_isSharedCheck_2637_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fuel_2626_);
                    v___x_2638_ = 0;
                    v___x_2639_ = crate::leanh::lean_box((v___x_2638_) as usize);
                    v___x_2640_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2640_, 0, v___x_2639_);
                    return v___x_2640_;
                }
            }
            1 => {
                v___x_2631_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2632_ = lean_nat_dec_eq(v_n_2627_, v___x_2631_);
                crate::leanh::lean_dec(v_n_2627_);
                v___x_2633_ = crate::leanh::lean_box((v___x_2632_) as usize);
                if v_isShared_2630_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2629_, 0, v___x_2633_);
                    v___x_2635_ = v___x_2629_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2636_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
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
    mut v_a_2641_: *mut crate::leanh::LeanObject,
    mut v_a_2642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2643_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v_a_2641_);
    crate::leanh::lean_dec(v_a_2641_);
    return v_res_2643_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel(
    mut v_a_2644_: *mut crate::leanh::LeanObject,
    mut v_a_2645_: *mut crate::leanh::LeanObject,
    mut v_a_2646_: *mut crate::leanh::LeanObject,
    mut v_a_2647_: *mut crate::leanh::LeanObject,
    mut v_a_2648_: *mut crate::leanh::LeanObject,
    mut v_a_2649_: *mut crate::leanh::LeanObject,
    mut v_a_2650_: *mut crate::leanh::LeanObject,
    mut v_a_2651_: *mut crate::leanh::LeanObject,
    mut v_a_2652_: *mut crate::leanh::LeanObject,
    mut v_a_2653_: *mut crate::leanh::LeanObject,
    mut v_a_2654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2656_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v_a_2645_);
    return v___x_2656_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___boxed(
    mut v_a_2657_: *mut crate::leanh::LeanObject,
    mut v_a_2658_: *mut crate::leanh::LeanObject,
    mut v_a_2659_: *mut crate::leanh::LeanObject,
    mut v_a_2660_: *mut crate::leanh::LeanObject,
    mut v_a_2661_: *mut crate::leanh::LeanObject,
    mut v_a_2662_: *mut crate::leanh::LeanObject,
    mut v_a_2663_: *mut crate::leanh::LeanObject,
    mut v_a_2664_: *mut crate::leanh::LeanObject,
    mut v_a_2665_: *mut crate::leanh::LeanObject,
    mut v_a_2666_: *mut crate::leanh::LeanObject,
    mut v_a_2667_: *mut crate::leanh::LeanObject,
    mut v_a_2668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2669_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel(
        v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_,
        v_a_2665_, v_a_2666_, v_a_2667_,
    );
    crate::leanh::lean_dec(v_a_2667_);
    crate::leanh::lean_dec_ref(v_a_2666_);
    crate::leanh::lean_dec(v_a_2665_);
    crate::leanh::lean_dec_ref(v_a_2664_);
    crate::leanh::lean_dec(v_a_2663_);
    crate::leanh::lean_dec_ref(v_a_2662_);
    crate::leanh::lean_dec(v_a_2661_);
    crate::leanh::lean_dec_ref(v_a_2660_);
    crate::leanh::lean_dec(v_a_2659_);
    crate::leanh::lean_dec(v_a_2658_);
    crate::leanh::lean_dec_ref(v_a_2657_);
    return v_res_2669_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(
    mut v_a_2670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_specBackwardRuleCache_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitBackwardRuleCache_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invariants_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vcs_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpState_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fuel_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineHandledInvariants_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preTacFailed_2680_: u8 = 0;
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2683_: u8 = 0;
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2694_: u8 = 0;
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2697_: u8 = 0;
    let mut v_one_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2703_: u8 = 0;
    let mut v_unused_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2672_ = lean_st_ref_take(v_a_2670_);
                v_specBackwardRuleCache_2673_ = crate::leanh::lean_ctor_get(v___x_2672_, 0);
                v_splitBackwardRuleCache_2674_ = crate::leanh::lean_ctor_get(v___x_2672_, 1);
                v_invariants_2675_ = crate::leanh::lean_ctor_get(v___x_2672_, 2);
                v_vcs_2676_ = crate::leanh::lean_ctor_get(v___x_2672_, 3);
                v_simpState_2677_ = crate::leanh::lean_ctor_get(v___x_2672_, 4);
                v_fuel_2678_ = crate::leanh::lean_ctor_get(v___x_2672_, 5);
                v_inlineHandledInvariants_2679_ = crate::leanh::lean_ctor_get(v___x_2672_, 6);
                v_preTacFailed_2680_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2672_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_isSharedCheck_2705_ = (!crate::leanh::lean_is_exclusive(v___x_2672_)) as u8;
                if v_isSharedCheck_2705_ == 0 {
                    v___x_2682_ = v___x_2672_;
                    v_isShared_2683_ = v_isSharedCheck_2705_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineHandledInvariants_2679_);
                    crate::leanh::lean_inc(v_fuel_2678_);
                    crate::leanh::lean_inc(v_simpState_2677_);
                    crate::leanh::lean_inc(v_vcs_2676_);
                    crate::leanh::lean_inc(v_invariants_2675_);
                    crate::leanh::lean_inc(v_splitBackwardRuleCache_2674_);
                    crate::leanh::lean_inc(v_specBackwardRuleCache_2673_);
                    crate::leanh::lean_dec(v___x_2672_);
                    v___x_2682_ = crate::leanh::lean_box(0);
                    v_isShared_2683_ = v_isSharedCheck_2705_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2684_ = crate::leanh::lean_box(0);
                if crate::leanh::lean_obj_tag(v_fuel_2678_) == 0 {
                    v_n_2692_ = crate::leanh::lean_ctor_get(v_fuel_2678_, 0);
                    v_zero_2693_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_isZero_2694_ = lean_nat_dec_eq(v_n_2692_, v_zero_2693_);
                    if v_isZero_2694_ == 0 {
                        crate::leanh::lean_inc(v_n_2692_);
                        v_isSharedCheck_2703_ =
                            (!crate::leanh::lean_is_exclusive(v_fuel_2678_)) as u8;
                        if v_isSharedCheck_2703_ == 0 {
                            v_unused_2704_ = crate::leanh::lean_ctor_get(v_fuel_2678_, 0);
                            crate::leanh::lean_dec(v_unused_2704_);
                            v___x_2696_ = v_fuel_2678_;
                            v_isShared_2697_ = v_isSharedCheck_2703_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_fuel_2678_);
                            v___x_2696_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_2682_, 5, v___y_2686_);
                    v___x_2688_ = v___x_2682_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2691_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2691_,
                        0,
                        v_specBackwardRuleCache_2673_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2691_,
                        1,
                        v_splitBackwardRuleCache_2674_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 2, v_invariants_2675_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 3, v_vcs_2676_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 4, v_simpState_2677_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 5, v___y_2686_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2691_,
                        6,
                        v_inlineHandledInvariants_2679_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2691_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_preTacFailed_2680_,
                    );
                    v___x_2688_ = v_reuseFailAlloc_2691_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2689_ = lean_st_ref_set(v_a_2670_, v___x_2688_);
                v___x_2690_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2690_, 0, v___x_2684_);
                return v___x_2690_;
            }
            4 => {
                v_one_2698_ = crate::leanh::lean_unsigned_to_nat(1);
                v_n_2699_ = lean_nat_sub(v_n_2692_, v_one_2698_);
                crate::leanh::lean_dec(v_n_2692_);
                if v_isShared_2697_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2696_, 0, v_n_2699_);
                    v___x_2701_ = v___x_2696_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2702_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_n_2699_);
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
    mut v_a_2706_: *mut crate::leanh::LeanObject,
    mut v_a_2707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2708_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v_a_2706_);
    crate::leanh::lean_dec(v_a_2706_);
    return v_res_2708_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne(
    mut v_a_2709_: *mut crate::leanh::LeanObject,
    mut v_a_2710_: *mut crate::leanh::LeanObject,
    mut v_a_2711_: *mut crate::leanh::LeanObject,
    mut v_a_2712_: *mut crate::leanh::LeanObject,
    mut v_a_2713_: *mut crate::leanh::LeanObject,
    mut v_a_2714_: *mut crate::leanh::LeanObject,
    mut v_a_2715_: *mut crate::leanh::LeanObject,
    mut v_a_2716_: *mut crate::leanh::LeanObject,
    mut v_a_2717_: *mut crate::leanh::LeanObject,
    mut v_a_2718_: *mut crate::leanh::LeanObject,
    mut v_a_2719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2721_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v_a_2710_);
    return v___x_2721_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___boxed(
    mut v_a_2722_: *mut crate::leanh::LeanObject,
    mut v_a_2723_: *mut crate::leanh::LeanObject,
    mut v_a_2724_: *mut crate::leanh::LeanObject,
    mut v_a_2725_: *mut crate::leanh::LeanObject,
    mut v_a_2726_: *mut crate::leanh::LeanObject,
    mut v_a_2727_: *mut crate::leanh::LeanObject,
    mut v_a_2728_: *mut crate::leanh::LeanObject,
    mut v_a_2729_: *mut crate::leanh::LeanObject,
    mut v_a_2730_: *mut crate::leanh::LeanObject,
    mut v_a_2731_: *mut crate::leanh::LeanObject,
    mut v_a_2732_: *mut crate::leanh::LeanObject,
    mut v_a_2733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2734_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne(
        v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_,
        v_a_2730_, v_a_2731_, v_a_2732_,
    );
    crate::leanh::lean_dec(v_a_2732_);
    crate::leanh::lean_dec_ref(v_a_2731_);
    crate::leanh::lean_dec(v_a_2730_);
    crate::leanh::lean_dec_ref(v_a_2729_);
    crate::leanh::lean_dec(v_a_2728_);
    crate::leanh::lean_dec_ref(v_a_2727_);
    crate::leanh::lean_dec(v_a_2726_);
    crate::leanh::lean_dec_ref(v_a_2725_);
    crate::leanh::lean_dec(v_a_2724_);
    crate::leanh::lean_dec(v_a_2723_);
    crate::leanh::lean_dec_ref(v_a_2722_);
    return v_res_2734_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Apply(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default =
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default();
    crate::leanh::lean_mark_persistent(
        l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default,
    );
    l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope =
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_VCGen_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Apply(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
}
