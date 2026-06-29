// Lean compiler output
// Module: Lean.Compiler.LCNF.LiveVars
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.DependsOn
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_uget_borrowed,
    lean_array_uset, lean_mk_array, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div,
    lean_nat_mul, lean_panic_fn_borrowed, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_land, lean_usize_of_nat,
    lean_usize_sub,
};
use crate::r#gen::Init::Control::State::{
    l_StateT_bind, l_StateT_instMonad___redArg___lam__1, l_StateT_instMonad___redArg___lam__4,
    l_StateT_instMonad___redArg___lam__7, l_StateT_instMonad___redArg___lam__9, l_StateT_map,
    l_StateT_pure,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedForall___redArg___lam__0___boxed, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM, l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed,
    runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::r#gen::Lean::Compiler::LCNF::DependsOn::{
    initialize_Lean_Compiler_LCNF_DependsOn,
    l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn,
    l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn,
    runtime_initialize_Lean_Compiler_LCNF_DependsOn,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_instBEqFVarId_beq, l_Lean_instBEqFVarId_beq___boxed,
    l_Lean_instEmptyCollectionFVarIdHashSet, l_Lean_instHashableFVarId_hash,
    l_Lean_instHashableFVarId_hash___boxed, l_Lean_instSingletonFVarIdFVarIdSet___lam__0,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg;
pub static l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqFVarId_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableFVarId_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__2_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__1_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 76, 105, 118, 101, 86, 97, 114, 115, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 67, 111, 100, 101, 46, 105, 115, 70, 86, 97, 114, 76, 105, 118, 101, 73, 110, 46, 103, 111, 0]};
static mut l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__0_value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 76, 105, 118, 101, 86, 97, 114, 115, 0]};
static mut l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar___redArg(
    mut v_fvarId_664_: *mut crate::leanh::LeanObject,
    mut v_x_665_: *mut crate::leanh::LeanObject,
    mut v_a_666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_668_: u8 = 0;
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_668_ = l_Lean_instBEqFVarId_beq(v_x_665_, v_fvarId_664_);
    v___x_669_ = crate::leanh::lean_box((v___x_668_) as usize);
    v___x_670_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_670_, 0, v___x_669_);
    crate::leanh::lean_ctor_set(v___x_670_, 1, v_a_666_);
    v___x_671_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_671_, 0, v___x_670_);
    return v___x_671_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar___redArg___boxed(
    mut v_fvarId_672_: *mut crate::leanh::LeanObject,
    mut v_x_673_: *mut crate::leanh::LeanObject,
    mut v_a_674_: *mut crate::leanh::LeanObject,
    mut v_a_675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_676_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar___redArg(v_fvarId_672_, v_x_673_, v_a_674_);
    crate::leanh::lean_dec(v_x_673_);
    crate::leanh::lean_dec(v_fvarId_672_);
    return v_res_676_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar(
    mut v_fvarId_677_: *mut crate::leanh::LeanObject,
    mut v_x_678_: *mut crate::leanh::LeanObject,
    mut v_a_679_: *mut crate::leanh::LeanObject,
    mut v_a_680_: *mut crate::leanh::LeanObject,
    mut v_a_681_: *mut crate::leanh::LeanObject,
    mut v_a_682_: *mut crate::leanh::LeanObject,
    mut v_a_683_: *mut crate::leanh::LeanObject,
    mut v_a_684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_686_: u8 = 0;
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_686_ = l_Lean_instBEqFVarId_beq(v_x_678_, v_fvarId_677_);
    v___x_687_ = crate::leanh::lean_box((v___x_686_) as usize);
    v___x_688_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_688_, 0, v___x_687_);
    crate::leanh::lean_ctor_set(v___x_688_, 1, v_a_680_);
    v___x_689_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_689_, 0, v___x_688_);
    return v___x_689_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar___boxed(
    mut v_fvarId_690_: *mut crate::leanh::LeanObject,
    mut v_x_691_: *mut crate::leanh::LeanObject,
    mut v_a_692_: *mut crate::leanh::LeanObject,
    mut v_a_693_: *mut crate::leanh::LeanObject,
    mut v_a_694_: *mut crate::leanh::LeanObject,
    mut v_a_695_: *mut crate::leanh::LeanObject,
    mut v_a_696_: *mut crate::leanh::LeanObject,
    mut v_a_697_: *mut crate::leanh::LeanObject,
    mut v_a_698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_699_ =
        l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_visitVar(
            v_fvarId_690_,
            v_x_691_,
            v_a_692_,
            v_a_693_,
            v_a_694_,
            v_a_695_,
            v_a_696_,
            v_a_697_,
        );
    crate::leanh::lean_dec(v_a_697_);
    crate::leanh::lean_dec_ref(v_a_696_);
    crate::leanh::lean_dec(v_a_695_);
    crate::leanh::lean_dec_ref(v_a_694_);
    crate::leanh::lean_dec_ref(v_a_692_);
    crate::leanh::lean_dec(v_x_691_);
    crate::leanh::lean_dec(v_fvarId_690_);
    return v_res_699_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg(
    mut v_jp_702_: *mut crate::leanh::LeanObject,
    mut v_a_703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_705_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__0;
    v___x_706_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__1;
    v___x_707_ = crate::leanh::lean_box(0);
    v___x_708_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v___x_705_, v___x_706_, v_a_703_, v_jp_702_, v___x_707_,
    );
    v___x_709_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_709_, 0, v___x_707_);
    crate::leanh::lean_ctor_set(v___x_709_, 1, v___x_708_);
    v___x_710_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_710_, 0, v___x_709_);
    return v___x_710_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___boxed(
    mut v_jp_711_: *mut crate::leanh::LeanObject,
    mut v_a_712_: *mut crate::leanh::LeanObject,
    mut v_a_713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_714_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg(v_jp_711_, v_a_712_);
    return v_res_714_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited(
    mut v_jp_715_: *mut crate::leanh::LeanObject,
    mut v_a_716_: *mut crate::leanh::LeanObject,
    mut v_a_717_: *mut crate::leanh::LeanObject,
    mut v_a_718_: *mut crate::leanh::LeanObject,
    mut v_a_719_: *mut crate::leanh::LeanObject,
    mut v_a_720_: *mut crate::leanh::LeanObject,
    mut v_a_721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_723_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__0;
    v___x_724_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___redArg___closed__1;
    v___x_725_ = crate::leanh::lean_box(0);
    v___x_726_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v___x_723_, v___x_724_, v_a_717_, v_jp_715_, v___x_725_,
    );
    v___x_727_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_727_, 0, v___x_725_);
    crate::leanh::lean_ctor_set(v___x_727_, 1, v___x_726_);
    v___x_728_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_728_, 0, v___x_727_);
    return v___x_728_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited___boxed(
    mut v_jp_729_: *mut crate::leanh::LeanObject,
    mut v_a_730_: *mut crate::leanh::LeanObject,
    mut v_a_731_: *mut crate::leanh::LeanObject,
    mut v_a_732_: *mut crate::leanh::LeanObject,
    mut v_a_733_: *mut crate::leanh::LeanObject,
    mut v_a_734_: *mut crate::leanh::LeanObject,
    mut v_a_735_: *mut crate::leanh::LeanObject,
    mut v_a_736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_737_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_markJpVisited(v_jp_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
    crate::leanh::lean_dec(v_a_735_);
    crate::leanh::lean_dec_ref(v_a_734_);
    crate::leanh::lean_dec(v_a_733_);
    crate::leanh::lean_dec_ref(v_a_732_);
    crate::leanh::lean_dec_ref(v_a_730_);
    return v_res_737_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_738_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_738_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2(
    mut v_msg_743_: *mut crate::leanh::LeanObject,
    mut v___y_744_: *mut crate::leanh::LeanObject,
    mut v___y_745_: *mut crate::leanh::LeanObject,
    mut v___y_746_: *mut crate::leanh::LeanObject,
    mut v___y_747_: *mut crate::leanh::LeanObject,
    mut v___y_748_: *mut crate::leanh::LeanObject,
    mut v___y_749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_756_: u8 = 0;
    let mut v_toFunctor_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_763_: u8 = 0;
    let mut v___f_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_780_: u8 = 0;
    let mut v_toFunctor_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_787_: u8 = 0;
    let mut v___f_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: u8 = 0;
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_17249__overap_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_818_: u8 = 0;
    let mut v_unused_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_820_: u8 = 0;
    let mut v_unused_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_824_: u8 = 0;
    let mut v_unused_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_826_: u8 = 0;
    let mut v_unused_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_751_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__0);
                v___x_752_ = l_StateRefT_x27_instMonad___redArg(v___x_751_);
                v_toApplicative_753_ = crate::leanh::lean_ctor_get(v___x_752_, 0);
                v_isSharedCheck_826_ = (!crate::leanh::lean_is_exclusive(v___x_752_)) as u8;
                if v_isSharedCheck_826_ == 0 {
                    v_unused_827_ = crate::leanh::lean_ctor_get(v___x_752_, 1);
                    crate::leanh::lean_dec(v_unused_827_);
                    v___x_755_ = v___x_752_;
                    v_isShared_756_ = v_isSharedCheck_826_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_753_);
                    crate::leanh::lean_dec(v___x_752_);
                    v___x_755_ = crate::leanh::lean_box(0);
                    v_isShared_756_ = v_isSharedCheck_826_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_757_ = crate::leanh::lean_ctor_get(v_toApplicative_753_, 0);
                v_toSeq_758_ = crate::leanh::lean_ctor_get(v_toApplicative_753_, 2);
                v_toSeqLeft_759_ = crate::leanh::lean_ctor_get(v_toApplicative_753_, 3);
                v_toSeqRight_760_ = crate::leanh::lean_ctor_get(v_toApplicative_753_, 4);
                v_isSharedCheck_824_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_753_)) as u8;
                if v_isSharedCheck_824_ == 0 {
                    v_unused_825_ = crate::leanh::lean_ctor_get(v_toApplicative_753_, 1);
                    crate::leanh::lean_dec(v_unused_825_);
                    v___x_762_ = v_toApplicative_753_;
                    v_isShared_763_ = v_isSharedCheck_824_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_760_);
                    crate::leanh::lean_inc(v_toSeqLeft_759_);
                    crate::leanh::lean_inc(v_toSeq_758_);
                    crate::leanh::lean_inc(v_toFunctor_757_);
                    crate::leanh::lean_dec(v_toApplicative_753_);
                    v___x_762_ = crate::leanh::lean_box(0);
                    v_isShared_763_ = v_isSharedCheck_824_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_764_ = l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__1;
                v___f_765_ = l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_757_);
                v___f_766_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_766_, 0, v_toFunctor_757_);
                v___f_767_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_767_, 0, v_toFunctor_757_);
                v___x_768_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_768_, 0, v___f_766_);
                crate::leanh::lean_ctor_set(v___x_768_, 1, v___f_767_);
                v___f_769_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_769_, 0, v_toSeqRight_760_);
                v___f_770_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_770_, 0, v_toSeqLeft_759_);
                v___f_771_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_771_, 0, v_toSeq_758_);
                if v_isShared_763_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_762_, 4, v___f_769_);
                    crate::leanh::lean_ctor_set(v___x_762_, 3, v___f_770_);
                    crate::leanh::lean_ctor_set(v___x_762_, 2, v___f_771_);
                    crate::leanh::lean_ctor_set(v___x_762_, 1, v___f_764_);
                    crate::leanh::lean_ctor_set(v___x_762_, 0, v___x_768_);
                    v___x_773_ = v___x_762_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_823_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_823_, 1, v___f_764_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_823_, 2, v___f_771_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_823_, 3, v___f_770_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_823_, 4, v___f_769_);
                    v___x_773_ = v_reuseFailAlloc_823_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_756_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_755_, 1, v___f_765_);
                    crate::leanh::lean_ctor_set(v___x_755_, 0, v___x_773_);
                    v___x_775_ = v___x_755_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_822_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_773_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_822_, 1, v___f_765_);
                    v___x_775_ = v_reuseFailAlloc_822_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_776_ = l_StateRefT_x27_instMonad___redArg(v___x_775_);
                v_toApplicative_777_ = crate::leanh::lean_ctor_get(v___x_776_, 0);
                v_isSharedCheck_820_ = (!crate::leanh::lean_is_exclusive(v___x_776_)) as u8;
                if v_isSharedCheck_820_ == 0 {
                    v_unused_821_ = crate::leanh::lean_ctor_get(v___x_776_, 1);
                    crate::leanh::lean_dec(v_unused_821_);
                    v___x_779_ = v___x_776_;
                    v_isShared_780_ = v_isSharedCheck_820_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_777_);
                    crate::leanh::lean_dec(v___x_776_);
                    v___x_779_ = crate::leanh::lean_box(0);
                    v_isShared_780_ = v_isSharedCheck_820_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_781_ = crate::leanh::lean_ctor_get(v_toApplicative_777_, 0);
                v_toSeq_782_ = crate::leanh::lean_ctor_get(v_toApplicative_777_, 2);
                v_toSeqLeft_783_ = crate::leanh::lean_ctor_get(v_toApplicative_777_, 3);
                v_toSeqRight_784_ = crate::leanh::lean_ctor_get(v_toApplicative_777_, 4);
                v_isSharedCheck_818_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_777_)) as u8;
                if v_isSharedCheck_818_ == 0 {
                    v_unused_819_ = crate::leanh::lean_ctor_get(v_toApplicative_777_, 1);
                    crate::leanh::lean_dec(v_unused_819_);
                    v___x_786_ = v_toApplicative_777_;
                    v_isShared_787_ = v_isSharedCheck_818_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_784_);
                    crate::leanh::lean_inc(v_toSeqLeft_783_);
                    crate::leanh::lean_inc(v_toSeq_782_);
                    crate::leanh::lean_inc(v_toFunctor_781_);
                    crate::leanh::lean_dec(v_toApplicative_777_);
                    v___x_786_ = crate::leanh::lean_box(0);
                    v_isShared_787_ = v_isSharedCheck_818_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_788_ = l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__3;
                v___f_789_ = l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_781_);
                v___f_790_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_790_, 0, v_toFunctor_781_);
                v___f_791_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_791_, 0, v_toFunctor_781_);
                v___x_792_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_792_, 0, v___f_790_);
                crate::leanh::lean_ctor_set(v___x_792_, 1, v___f_791_);
                v___f_793_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_793_, 0, v_toSeqRight_784_);
                v___f_794_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_794_, 0, v_toSeqLeft_783_);
                v___f_795_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_795_, 0, v_toSeq_782_);
                if v_isShared_787_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_786_, 4, v___f_793_);
                    crate::leanh::lean_ctor_set(v___x_786_, 3, v___f_794_);
                    crate::leanh::lean_ctor_set(v___x_786_, 2, v___f_795_);
                    crate::leanh::lean_ctor_set(v___x_786_, 1, v___f_788_);
                    crate::leanh::lean_ctor_set(v___x_786_, 0, v___x_792_);
                    v___x_797_ = v___x_786_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_817_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_792_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_817_, 1, v___f_788_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_817_, 2, v___f_795_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_817_, 3, v___f_794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_817_, 4, v___f_793_);
                    v___x_797_ = v_reuseFailAlloc_817_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_780_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_779_, 1, v___f_789_);
                    crate::leanh::lean_ctor_set(v___x_779_, 0, v___x_797_);
                    v___x_799_ = v___x_779_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_816_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_797_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_816_, 1, v___f_789_);
                    v___x_799_ = v_reuseFailAlloc_816_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_inc_ref_n(v___x_799_, 6);
                v___f_800_ = crate::leanh::lean_alloc_closure(
                    l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_800_, 0, v___x_799_);
                v___f_801_ = crate::leanh::lean_alloc_closure(
                    l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_801_, 0, v___x_799_);
                v___f_802_ = crate::leanh::lean_alloc_closure(
                    l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_802_, 0, v___x_799_);
                v___f_803_ = crate::leanh::lean_alloc_closure(
                    l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_803_, 0, v___x_799_);
                v___x_804_ =
                    crate::leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
                crate::leanh::lean_closure_set(v___x_804_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_804_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_804_, 2, v___x_799_);
                v___x_805_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_805_, 0, v___x_804_);
                crate::leanh::lean_ctor_set(v___x_805_, 1, v___f_800_);
                v___x_806_ =
                    crate::leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
                crate::leanh::lean_closure_set(v___x_806_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_806_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_806_, 2, v___x_799_);
                v___x_807_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_807_, 0, v___x_805_);
                crate::leanh::lean_ctor_set(v___x_807_, 1, v___x_806_);
                crate::leanh::lean_ctor_set(v___x_807_, 2, v___f_801_);
                crate::leanh::lean_ctor_set(v___x_807_, 3, v___f_802_);
                crate::leanh::lean_ctor_set(v___x_807_, 4, v___f_803_);
                v___x_808_ =
                    crate::leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
                crate::leanh::lean_closure_set(v___x_808_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_808_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_808_, 2, v___x_799_);
                v___x_809_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_809_, 0, v___x_807_);
                crate::leanh::lean_ctor_set(v___x_809_, 1, v___x_808_);
                v___x_810_ = 0;
                v___x_811_ = crate::leanh::lean_box((v___x_810_) as usize);
                v___x_812_ = l_instInhabitedOfMonad___redArg(v___x_809_, v___x_811_);
                v___f_813_ = crate::leanh::lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_813_, 0, v___x_812_);
                v___x_17249__overap_814_ = lean_panic_fn_borrowed(v___f_813_, v_msg_743_);
                crate::leanh::lean_dec_ref(v___f_813_);
                crate::leanh::lean_inc(v___y_749_);
                crate::leanh::lean_inc_ref(v___y_748_);
                crate::leanh::lean_inc(v___y_747_);
                crate::leanh::lean_inc_ref(v___y_746_);
                crate::leanh::lean_inc_ref(v___y_744_);
                v___x_815_ = crate::leanh::lean_apply_7(
                    v___x_17249__overap_814_,
                    v___y_744_,
                    v___y_745_,
                    v___y_746_,
                    v___y_747_,
                    v___y_748_,
                    v___y_749_,
                    crate::leanh::lean_box(0),
                );
                return v___x_815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2___boxed(
    mut v_msg_828_: *mut crate::leanh::LeanObject,
    mut v___y_829_: *mut crate::leanh::LeanObject,
    mut v___y_830_: *mut crate::leanh::LeanObject,
    mut v___y_831_: *mut crate::leanh::LeanObject,
    mut v___y_832_: *mut crate::leanh::LeanObject,
    mut v___y_833_: *mut crate::leanh::LeanObject,
    mut v___y_834_: *mut crate::leanh::LeanObject,
    mut v___y_835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_836_ = l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2(v_msg_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
    crate::leanh::lean_dec(v___y_834_);
    crate::leanh::lean_dec_ref(v___y_833_);
    crate::leanh::lean_dec(v___y_832_);
    crate::leanh::lean_dec_ref(v___y_831_);
    crate::leanh::lean_dec_ref(v___y_829_);
    return v_res_836_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(
    mut v_a_837_: *mut crate::leanh::LeanObject,
    mut v_x_838_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_839_: u8 = 0;
    let mut v_key_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_838_) == 0 {
                    v___x_839_ = 0;
                    return v___x_839_;
                } else {
                    v_key_840_ = crate::leanh::lean_ctor_get(v_x_838_, 0);
                    v_tail_841_ = crate::leanh::lean_ctor_get(v_x_838_, 2);
                    v___x_842_ = l_Lean_instBEqFVarId_beq(v_key_840_, v_a_837_);
                    if v___x_842_ == 0 {
                        v_x_838_ = v_tail_841_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_842_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg___boxed(
    mut v_a_844_: *mut crate::leanh::LeanObject,
    mut v_x_845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_846_: u8 = 0;
    let mut v_r_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_846_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(v_a_844_, v_x_845_);
    crate::leanh::lean_dec(v_x_845_);
    crate::leanh::lean_dec(v_a_844_);
    v_r_847_ = crate::leanh::lean_box((v_res_846_) as usize);
    return v_r_847_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(
    mut v_m_848_: *mut crate::leanh::LeanObject,
    mut v_a_849_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: u64 = 0;
    let mut v___x_853_: u64 = 0;
    let mut v___x_854_: u64 = 0;
    let mut v_fold_855_: u64 = 0;
    let mut v___x_856_: u64 = 0;
    let mut v___x_857_: u64 = 0;
    let mut v___x_858_: u64 = 0;
    let mut v___x_859_: usize = 0;
    let mut v___x_860_: usize = 0;
    let mut v___x_861_: usize = 0;
    let mut v___x_862_: usize = 0;
    let mut v___x_863_: usize = 0;
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: u8 = 0;
    v_buckets_850_ = crate::leanh::lean_ctor_get(v_m_848_, 1);
    v___x_851_ = lean_array_get_size(v_buckets_850_);
    v___x_852_ = l_Lean_instHashableFVarId_hash(v_a_849_);
    v___x_853_ = 32u64;
    v___x_854_ = lean_uint64_shift_right(v___x_852_, v___x_853_);
    v_fold_855_ = lean_uint64_xor(v___x_852_, v___x_854_);
    v___x_856_ = 16u64;
    v___x_857_ = lean_uint64_shift_right(v_fold_855_, v___x_856_);
    v___x_858_ = lean_uint64_xor(v_fold_855_, v___x_857_);
    v___x_859_ = lean_uint64_to_usize(v___x_858_);
    v___x_860_ = lean_usize_of_nat(v___x_851_);
    v___x_861_ = 1usize;
    v___x_862_ = lean_usize_sub(v___x_860_, v___x_861_);
    v___x_863_ = lean_usize_land(v___x_859_, v___x_862_);
    v___x_864_ = lean_array_uget_borrowed(v_buckets_850_, v___x_863_);
    v___x_865_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(v_a_849_, v___x_864_);
    return v___x_865_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg___boxed(
    mut v_m_866_: *mut crate::leanh::LeanObject,
    mut v_a_867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_868_: u8 = 0;
    let mut v_r_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_868_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_m_866_, v_a_867_);
    crate::leanh::lean_dec(v_a_867_);
    crate::leanh::lean_dec_ref(v_m_866_);
    v_r_869_ = crate::leanh::lean_box((v_res_868_) as usize);
    return v_r_869_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3(
    mut v_a_870_: *mut crate::leanh::LeanObject,
    mut v_as_871_: *mut crate::leanh::LeanObject,
    mut v_i_872_: usize,
    mut v_stop_873_: usize,
) -> u8 {
    let mut v___x_874_: u8 = 0;
    let mut v_targetSet_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: u8 = 0;
    let mut v___x_878_: u8 = 0;
    let mut v___x_879_: usize = 0;
    let mut v___x_880_: usize = 0;
    let mut v___x_882_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_874_ = lean_usize_dec_eq(v_i_872_, v_stop_873_);
                if v___x_874_ == 0 {
                    v_targetSet_875_ = crate::leanh::lean_ctor_get(v_a_870_, 0);
                    v___x_876_ = lean_array_uget_borrowed(v_as_871_, v_i_872_);
                    v___x_877_ = 1;
                    v___x_878_ =
                        l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(
                            v___x_877_,
                            v___x_876_,
                            v_targetSet_875_,
                        );
                    if v___x_878_ == 0 {
                        v___x_879_ = 1usize;
                        v___x_880_ = lean_usize_add(v_i_872_, v___x_879_);
                        v_i_872_ = v___x_880_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_878_;
                    }
                } else {
                    v___x_882_ = 0;
                    return v___x_882_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3___boxed(
    mut v_a_883_: *mut crate::leanh::LeanObject,
    mut v_as_884_: *mut crate::leanh::LeanObject,
    mut v_i_885_: *mut crate::leanh::LeanObject,
    mut v_stop_886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_887_: usize = 0;
    let mut v_stop_boxed_888_: usize = 0;
    let mut v_res_889_: u8 = 0;
    let mut v_r_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_887_ = crate::leanh::lean_unbox_usize(v_i_885_);
    crate::leanh::lean_dec(v_i_885_);
    v_stop_boxed_888_ = crate::leanh::lean_unbox_usize(v_stop_886_);
    crate::leanh::lean_dec(v_stop_886_);
    v_res_889_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3(v_a_883_, v_as_884_, v_i_boxed_887_, v_stop_boxed_888_);
    crate::leanh::lean_dec_ref(v_as_884_);
    crate::leanh::lean_dec_ref(v_a_883_);
    v_r_890_ = crate::leanh::lean_box((v_res_889_) as usize);
    return v_r_890_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3_spec__7___redArg(
    mut v_x_891_: *mut crate::leanh::LeanObject,
    mut v_x_892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_898_: u8 = 0;
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: u64 = 0;
    let mut v___x_901_: u64 = 0;
    let mut v___x_902_: u64 = 0;
    let mut v_fold_903_: u64 = 0;
    let mut v___x_904_: u64 = 0;
    let mut v___x_905_: u64 = 0;
    let mut v___x_906_: u64 = 0;
    let mut v___x_907_: usize = 0;
    let mut v___x_908_: usize = 0;
    let mut v___x_909_: usize = 0;
    let mut v___x_910_: usize = 0;
    let mut v___x_911_: usize = 0;
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_918_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_892_) == 0 {
                    return v_x_891_;
                } else {
                    v_key_893_ = crate::leanh::lean_ctor_get(v_x_892_, 0);
                    v_value_894_ = crate::leanh::lean_ctor_get(v_x_892_, 1);
                    v_tail_895_ = crate::leanh::lean_ctor_get(v_x_892_, 2);
                    v_isSharedCheck_918_ = (!crate::leanh::lean_is_exclusive(v_x_892_)) as u8;
                    if v_isSharedCheck_918_ == 0 {
                        v___x_897_ = v_x_892_;
                        v_isShared_898_ = v_isSharedCheck_918_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_895_);
                        crate::leanh::lean_inc(v_value_894_);
                        crate::leanh::lean_inc(v_key_893_);
                        crate::leanh::lean_dec(v_x_892_);
                        v___x_897_ = crate::leanh::lean_box(0);
                        v_isShared_898_ = v_isSharedCheck_918_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_899_ = lean_array_get_size(v_x_891_);
                v___x_900_ = l_Lean_instHashableFVarId_hash(v_key_893_);
                v___x_901_ = 32u64;
                v___x_902_ = lean_uint64_shift_right(v___x_900_, v___x_901_);
                v_fold_903_ = lean_uint64_xor(v___x_900_, v___x_902_);
                v___x_904_ = 16u64;
                v___x_905_ = lean_uint64_shift_right(v_fold_903_, v___x_904_);
                v___x_906_ = lean_uint64_xor(v_fold_903_, v___x_905_);
                v___x_907_ = lean_uint64_to_usize(v___x_906_);
                v___x_908_ = lean_usize_of_nat(v___x_899_);
                v___x_909_ = 1usize;
                v___x_910_ = lean_usize_sub(v___x_908_, v___x_909_);
                v___x_911_ = lean_usize_land(v___x_907_, v___x_910_);
                v___x_912_ = lean_array_uget_borrowed(v_x_891_, v___x_911_);
                crate::leanh::lean_inc(v___x_912_);
                if v_isShared_898_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_897_, 2, v___x_912_);
                    v___x_914_ = v___x_897_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_917_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_917_, 0, v_key_893_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_917_, 1, v_value_894_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_917_, 2, v___x_912_);
                    v___x_914_ = v_reuseFailAlloc_917_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_915_ = lean_array_uset(v_x_891_, v___x_911_, v___x_914_);
                v_x_891_ = v___x_915_;
                v_x_892_ = v_tail_895_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3___redArg(
    mut v_i_919_: *mut crate::leanh::LeanObject,
    mut v_source_920_: *mut crate::leanh::LeanObject,
    mut v_target_921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: u8 = 0;
    let mut v_es_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_922_ = lean_array_get_size(v_source_920_);
                v___x_923_ = lean_nat_dec_lt(v_i_919_, v___x_922_);
                if v___x_923_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_920_);
                    crate::leanh::lean_dec(v_i_919_);
                    return v_target_921_;
                } else {
                    v_es_924_ = lean_array_fget(v_source_920_, v_i_919_);
                    v___x_925_ = crate::leanh::lean_box(0);
                    v_source_926_ = lean_array_fset(v_source_920_, v_i_919_, v___x_925_);
                    v_target_927_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3_spec__7___redArg(v_target_921_, v_es_924_);
                    v___x_928_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_929_ = lean_nat_add(v_i_919_, v___x_928_);
                    crate::leanh::lean_dec(v_i_919_);
                    v_i_919_ = v___x_929_;
                    v_source_920_ = v_source_926_;
                    v_target_921_ = v_target_927_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1___redArg(
    mut v_data_931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_932_ = lean_array_get_size(v_data_931_);
    v___x_933_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_934_ = lean_nat_mul(v___x_932_, v___x_933_);
    v___x_935_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_936_ = crate::leanh::lean_box(0);
    v___x_937_ = lean_mk_array(v_nbuckets_934_, v___x_936_);
    v___x_938_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3___redArg(v___x_935_, v_data_931_, v___x_937_);
    return v___x_938_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(
    mut v_m_939_: *mut crate::leanh::LeanObject,
    mut v_a_940_: *mut crate::leanh::LeanObject,
    mut v_b_941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: u64 = 0;
    let mut v___x_946_: u64 = 0;
    let mut v___x_947_: u64 = 0;
    let mut v_fold_948_: u64 = 0;
    let mut v___x_949_: u64 = 0;
    let mut v___x_950_: u64 = 0;
    let mut v___x_951_: u64 = 0;
    let mut v___x_952_: usize = 0;
    let mut v___x_953_: usize = 0;
    let mut v___x_954_: usize = 0;
    let mut v___x_955_: usize = 0;
    let mut v___x_956_: usize = 0;
    let mut v_bkt_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: u8 = 0;
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_961_: u8 = 0;
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: u8 = 0;
    let mut v_val_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_979_: u8 = 0;
    let mut v_unused_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_942_ = crate::leanh::lean_ctor_get(v_m_939_, 0);
                v_buckets_943_ = crate::leanh::lean_ctor_get(v_m_939_, 1);
                v___x_944_ = lean_array_get_size(v_buckets_943_);
                v___x_945_ = l_Lean_instHashableFVarId_hash(v_a_940_);
                v___x_946_ = 32u64;
                v___x_947_ = lean_uint64_shift_right(v___x_945_, v___x_946_);
                v_fold_948_ = lean_uint64_xor(v___x_945_, v___x_947_);
                v___x_949_ = 16u64;
                v___x_950_ = lean_uint64_shift_right(v_fold_948_, v___x_949_);
                v___x_951_ = lean_uint64_xor(v_fold_948_, v___x_950_);
                v___x_952_ = lean_uint64_to_usize(v___x_951_);
                v___x_953_ = lean_usize_of_nat(v___x_944_);
                v___x_954_ = 1usize;
                v___x_955_ = lean_usize_sub(v___x_953_, v___x_954_);
                v___x_956_ = lean_usize_land(v___x_952_, v___x_955_);
                v_bkt_957_ = lean_array_uget_borrowed(v_buckets_943_, v___x_956_);
                v___x_958_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(v_a_940_, v_bkt_957_);
                if v___x_958_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_943_);
                    crate::leanh::lean_inc(v_size_942_);
                    v_isSharedCheck_979_ = (!crate::leanh::lean_is_exclusive(v_m_939_)) as u8;
                    if v_isSharedCheck_979_ == 0 {
                        v_unused_980_ = crate::leanh::lean_ctor_get(v_m_939_, 1);
                        crate::leanh::lean_dec(v_unused_980_);
                        v_unused_981_ = crate::leanh::lean_ctor_get(v_m_939_, 0);
                        crate::leanh::lean_dec(v_unused_981_);
                        v___x_960_ = v_m_939_;
                        v_isShared_961_ = v_isSharedCheck_979_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_939_);
                        v___x_960_ = crate::leanh::lean_box(0);
                        v_isShared_961_ = v_isSharedCheck_979_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_941_);
                    crate::leanh::lean_dec(v_a_940_);
                    return v_m_939_;
                }
            }
            1 => {
                v___x_962_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_963_ = lean_nat_add(v_size_942_, v___x_962_);
                crate::leanh::lean_dec(v_size_942_);
                crate::leanh::lean_inc(v_bkt_957_);
                v___x_964_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_964_, 0, v_a_940_);
                crate::leanh::lean_ctor_set(v___x_964_, 1, v_b_941_);
                crate::leanh::lean_ctor_set(v___x_964_, 2, v_bkt_957_);
                v_buckets_x27_965_ = lean_array_uset(v_buckets_943_, v___x_956_, v___x_964_);
                v___x_966_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_967_ = lean_nat_mul(v_size_x27_963_, v___x_966_);
                v___x_968_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_969_ = lean_nat_div(v___x_967_, v___x_968_);
                crate::leanh::lean_dec(v___x_967_);
                v___x_970_ = lean_array_get_size(v_buckets_x27_965_);
                v___x_971_ = lean_nat_dec_le(v___x_969_, v___x_970_);
                crate::leanh::lean_dec(v___x_969_);
                if v___x_971_ == 0 {
                    v_val_972_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1___redArg(v_buckets_x27_965_);
                    if v_isShared_961_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_960_, 1, v_val_972_);
                        crate::leanh::lean_ctor_set(v___x_960_, 0, v_size_x27_963_);
                        v___x_974_ = v___x_960_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_975_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_975_, 0, v_size_x27_963_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_975_, 1, v_val_972_);
                        v___x_974_ = v_reuseFailAlloc_975_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_961_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_960_, 1, v_buckets_x27_965_);
                        crate::leanh::lean_ctor_set(v___x_960_, 0, v_size_x27_963_);
                        v___x_977_ = v___x_960_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_978_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_978_, 0, v_size_x27_963_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_978_, 1, v_buckets_x27_965_);
                        v___x_977_ = v_reuseFailAlloc_978_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_974_;
            }
            3 => {
                return v___x_977_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_985_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__2;
    v___x_986_ = crate::leanh::lean_unsigned_to_nat(48);
    v___x_987_ = crate::leanh::lean_unsigned_to_nat(76);
    v___x_988_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__1;
    v___x_989_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__0;
    v___x_990_ =
        l_mkPanicMessageWithDecl(v___x_989_, v___x_988_, v___x_987_, v___x_986_, v___x_985_);
    return v___x_990_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(
    mut v_fvarId_991_: *mut crate::leanh::LeanObject,
    mut v_c_992_: *mut crate::leanh::LeanObject,
    mut v_a_993_: *mut crate::leanh::LeanObject,
    mut v_a_994_: *mut crate::leanh::LeanObject,
    mut v_a_995_: *mut crate::leanh::LeanObject,
    mut v_a_996_: *mut crate::leanh::LeanObject,
    mut v_a_997_: *mut crate::leanh::LeanObject,
    mut v_a_998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1004_: u8 = 0;
    let mut v_targetSet_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: u8 = 0;
    let mut v___x_1007_: u8 = 0;
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1014_: u8 = 0;
    let mut v_decl_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: u8 = 0;
    let mut v_snd_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1031_: u8 = 0;
    let mut v___y_1033_: u8 = 0;
    let mut v___x_1034_: u8 = 0;
    let mut v___x_1035_: u8 = 0;
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1048_: u8 = 0;
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1052_: u8 = 0;
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: u8 = 0;
    let mut v___x_1061_: usize = 0;
    let mut v___x_1062_: usize = 0;
    let mut v___x_1063_: u8 = 0;
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1067_: u8 = 0;
    let mut v_cases_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1071_: u8 = 0;
    let mut v_discr_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: u8 = 0;
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: u8 = 0;
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: usize = 0;
    let mut v___x_1089_: usize = 0;
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1096_: u8 = 0;
    let mut v_fvarId_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1100_: u8 = 0;
    let mut v___x_1101_: u8 = 0;
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1107_: u8 = 0;
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1110_: u8 = 0;
    let mut v___x_1111_: u8 = 0;
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1117_: u8 = 0;
    let mut v_unused_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: u8 = 0;
    let mut v_targetSet_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: u8 = 0;
    let mut v___x_1125_: u8 = 0;
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: u8 = 0;
    let mut v___x_1137_: u8 = 0;
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: u8 = 0;
    let mut v___x_1149_: u8 = 0;
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: u8 = 0;
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1168_: u8 = 0;
    let mut v___x_1169_: u8 = 0;
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1176_: u8 = 0;
    let mut v_fvarId_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: u8 = 0;
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match crate::leanh::lean_obj_tag(v_c_992_) {
                    0 => {
                        v_decl_1000_ = crate::leanh::lean_ctor_get(v_c_992_, 0);
                        v_k_1001_ = crate::leanh::lean_ctor_get(v_c_992_, 1);
                        v_isSharedCheck_1014_ = (!crate::leanh::lean_is_exclusive(v_c_992_)) as u8;
                        if v_isSharedCheck_1014_ == 0 {
                            v___x_1003_ = v_c_992_;
                            v_isShared_1004_ = v_isSharedCheck_1014_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_k_1001_);
                            crate::leanh::lean_inc(v_decl_1000_);
                            crate::leanh::lean_dec(v_c_992_);
                            v___x_1003_ = crate::leanh::lean_box(0);
                            v_isShared_1004_ = v_isSharedCheck_1014_;
                            state = 1;
                            continue;
                        }
                    }
                    2 => {
                        v_decl_1015_ = crate::leanh::lean_ctor_get(v_c_992_, 0);
                        crate::leanh::lean_inc_ref(v_decl_1015_);
                        v_k_1016_ = crate::leanh::lean_ctor_get(v_c_992_, 1);
                        crate::leanh::lean_inc_ref(v_k_1016_);
                        crate::leanh::lean_dec_ref_known(v_c_992_, 2);
                        v_fvarId_1017_ = crate::leanh::lean_ctor_get(v_decl_1015_, 0);
                        crate::leanh::lean_inc(v_fvarId_1017_);
                        v_value_1018_ = crate::leanh::lean_ctor_get(v_decl_1015_, 4);
                        crate::leanh::lean_inc_ref(v_value_1018_);
                        crate::leanh::lean_dec_ref(v_decl_1015_);
                        v___x_1019_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_991_, v_value_1018_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
                        if crate::leanh::lean_obj_tag(v___x_1019_) == 0 {
                            v_a_1020_ = crate::leanh::lean_ctor_get(v___x_1019_, 0);
                            crate::leanh::lean_inc(v_a_1020_);
                            v_fst_1021_ = crate::leanh::lean_ctor_get(v_a_1020_, 0);
                            v___x_1022_ = (crate::leanh::lean_unbox(v_fst_1021_) as u8);
                            if v___x_1022_ == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_1019_, 1);
                                v_snd_1023_ = crate::leanh::lean_ctor_get(v_a_1020_, 1);
                                crate::leanh::lean_inc(v_snd_1023_);
                                crate::leanh::lean_dec(v_a_1020_);
                                v___x_1024_ = crate::leanh::lean_box(0);
                                v___x_1025_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_snd_1023_, v_fvarId_1017_, v___x_1024_);
                                v_c_992_ = v_k_1016_;
                                v_a_994_ = v___x_1025_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_1020_);
                                crate::leanh::lean_dec(v_fvarId_1017_);
                                crate::leanh::lean_dec_ref(v_k_1016_);
                                return v___x_1019_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fvarId_1017_);
                            crate::leanh::lean_dec_ref(v_k_1016_);
                            return v___x_1019_;
                        }
                    }
                    3 => {
                        v_fvarId_1027_ = crate::leanh::lean_ctor_get(v_c_992_, 0);
                        v_args_1028_ = crate::leanh::lean_ctor_get(v_c_992_, 1);
                        v_isSharedCheck_1067_ = (!crate::leanh::lean_is_exclusive(v_c_992_)) as u8;
                        if v_isSharedCheck_1067_ == 0 {
                            v___x_1030_ = v_c_992_;
                            v_isShared_1031_ = v_isSharedCheck_1067_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_args_1028_);
                            crate::leanh::lean_inc(v_fvarId_1027_);
                            crate::leanh::lean_dec(v_c_992_);
                            v___x_1030_ = crate::leanh::lean_box(0);
                            v_isShared_1031_ = v_isSharedCheck_1067_;
                            state = 3;
                            continue;
                        }
                    }
                    4 => {
                        v_cases_1068_ = crate::leanh::lean_ctor_get(v_c_992_, 0);
                        v_isSharedCheck_1096_ = (!crate::leanh::lean_is_exclusive(v_c_992_)) as u8;
                        if v_isSharedCheck_1096_ == 0 {
                            v___x_1070_ = v_c_992_;
                            v_isShared_1071_ = v_isSharedCheck_1096_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_cases_1068_);
                            crate::leanh::lean_dec(v_c_992_);
                            v___x_1070_ = crate::leanh::lean_box(0);
                            v_isShared_1071_ = v_isSharedCheck_1096_;
                            state = 8;
                            continue;
                        }
                    }
                    5 => {
                        v_fvarId_1097_ = crate::leanh::lean_ctor_get(v_c_992_, 0);
                        v_isSharedCheck_1107_ = (!crate::leanh::lean_is_exclusive(v_c_992_)) as u8;
                        if v_isSharedCheck_1107_ == 0 {
                            v___x_1099_ = v_c_992_;
                            v_isShared_1100_ = v_isSharedCheck_1107_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fvarId_1097_);
                            crate::leanh::lean_dec(v_c_992_);
                            v___x_1099_ = crate::leanh::lean_box(0);
                            v_isShared_1100_ = v_isSharedCheck_1107_;
                            state = 12;
                            continue;
                        }
                    }
                    6 => {
                        v_isSharedCheck_1117_ = (!crate::leanh::lean_is_exclusive(v_c_992_)) as u8;
                        if v_isSharedCheck_1117_ == 0 {
                            v_unused_1118_ = crate::leanh::lean_ctor_get(v_c_992_, 0);
                            crate::leanh::lean_dec(v_unused_1118_);
                            v___x_1109_ = v_c_992_;
                            v_isShared_1110_ = v_isSharedCheck_1117_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_c_992_);
                            v___x_1109_ = crate::leanh::lean_box(0);
                            v_isShared_1110_ = v_isSharedCheck_1117_;
                            state = 14;
                            continue;
                        }
                    }
                    7 => {
                        v_fvarId_1119_ = crate::leanh::lean_ctor_get(v_c_992_, 0);
                        crate::leanh::lean_inc(v_fvarId_1119_);
                        v_y_1120_ = crate::leanh::lean_ctor_get(v_c_992_, 2);
                        crate::leanh::lean_inc(v_y_1120_);
                        v_k_1121_ = crate::leanh::lean_ctor_get(v_c_992_, 3);
                        crate::leanh::lean_inc_ref(v_k_1121_);
                        crate::leanh::lean_dec_ref_known(v_c_992_, 4);
                        v___x_1122_ = l_Lean_instBEqFVarId_beq(v_fvarId_1119_, v_fvarId_991_);
                        crate::leanh::lean_dec(v_fvarId_1119_);
                        if v___x_1122_ == 0 {
                            v_targetSet_1123_ = crate::leanh::lean_ctor_get(v_a_993_, 0);
                            v___x_1124_ = 1;
                            v___x_1125_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(v___x_1124_, v_y_1120_, v_targetSet_1123_);
                            crate::leanh::lean_dec(v_y_1120_);
                            if v___x_1125_ == 0 {
                                v_c_992_ = v_k_1121_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_k_1121_);
                                v___x_1127_ = crate::leanh::lean_box((v___x_1125_) as usize);
                                v___x_1128_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1128_, 0, v___x_1127_);
                                crate::leanh::lean_ctor_set(v___x_1128_, 1, v_a_994_);
                                v___x_1129_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1129_, 0, v___x_1128_);
                                return v___x_1129_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_k_1121_);
                            crate::leanh::lean_dec(v_y_1120_);
                            v___x_1130_ = crate::leanh::lean_box((v___x_1122_) as usize);
                            v___x_1131_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1131_, 0, v___x_1130_);
                            crate::leanh::lean_ctor_set(v___x_1131_, 1, v_a_994_);
                            v___x_1132_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1132_, 0, v___x_1131_);
                            return v___x_1132_;
                        }
                    }
                    8 => {
                        v_fvarId_1133_ = crate::leanh::lean_ctor_get(v_c_992_, 0);
                        crate::leanh::lean_inc(v_fvarId_1133_);
                        v_y_1134_ = crate::leanh::lean_ctor_get(v_c_992_, 2);
                        crate::leanh::lean_inc(v_y_1134_);
                        v_k_1135_ = crate::leanh::lean_ctor_get(v_c_992_, 3);
                        crate::leanh::lean_inc_ref(v_k_1135_);
                        crate::leanh::lean_dec_ref_known(v_c_992_, 4);
                        v___x_1136_ = l_Lean_instBEqFVarId_beq(v_fvarId_1133_, v_fvarId_991_);
                        crate::leanh::lean_dec(v_fvarId_1133_);
                        if v___x_1136_ == 0 {
                            v___x_1137_ = l_Lean_instBEqFVarId_beq(v_y_1134_, v_fvarId_991_);
                            crate::leanh::lean_dec(v_y_1134_);
                            if v___x_1137_ == 0 {
                                v_c_992_ = v_k_1135_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_k_1135_);
                                v___x_1139_ = crate::leanh::lean_box((v___x_1137_) as usize);
                                v___x_1140_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1140_, 0, v___x_1139_);
                                crate::leanh::lean_ctor_set(v___x_1140_, 1, v_a_994_);
                                v___x_1141_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1141_, 0, v___x_1140_);
                                return v___x_1141_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_k_1135_);
                            crate::leanh::lean_dec(v_y_1134_);
                            v___x_1142_ = crate::leanh::lean_box((v___x_1136_) as usize);
                            v___x_1143_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1143_, 0, v___x_1142_);
                            crate::leanh::lean_ctor_set(v___x_1143_, 1, v_a_994_);
                            v___x_1144_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1144_, 0, v___x_1143_);
                            return v___x_1144_;
                        }
                    }
                    9 => {
                        v_fvarId_1145_ = crate::leanh::lean_ctor_get(v_c_992_, 0);
                        crate::leanh::lean_inc(v_fvarId_1145_);
                        v_y_1146_ = crate::leanh::lean_ctor_get(v_c_992_, 3);
                        crate::leanh::lean_inc(v_y_1146_);
                        v_k_1147_ = crate::leanh::lean_ctor_get(v_c_992_, 5);
                        crate::leanh::lean_inc_ref(v_k_1147_);
                        crate::leanh::lean_dec_ref_known(v_c_992_, 6);
                        v___x_1148_ = l_Lean_instBEqFVarId_beq(v_fvarId_1145_, v_fvarId_991_);
                        crate::leanh::lean_dec(v_fvarId_1145_);
                        if v___x_1148_ == 0 {
                            v___x_1149_ = l_Lean_instBEqFVarId_beq(v_y_1146_, v_fvarId_991_);
                            crate::leanh::lean_dec(v_y_1146_);
                            if v___x_1149_ == 0 {
                                v_c_992_ = v_k_1147_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_k_1147_);
                                v___x_1151_ = crate::leanh::lean_box((v___x_1149_) as usize);
                                v___x_1152_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1152_, 0, v___x_1151_);
                                crate::leanh::lean_ctor_set(v___x_1152_, 1, v_a_994_);
                                v___x_1153_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1153_, 0, v___x_1152_);
                                return v___x_1153_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_k_1147_);
                            crate::leanh::lean_dec(v_y_1146_);
                            v___x_1154_ = crate::leanh::lean_box((v___x_1148_) as usize);
                            v___x_1155_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1155_, 0, v___x_1154_);
                            crate::leanh::lean_ctor_set(v___x_1155_, 1, v_a_994_);
                            v___x_1156_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1156_, 0, v___x_1155_);
                            return v___x_1156_;
                        }
                    }
                    12 => {
                        v_fvarId_1157_ = crate::leanh::lean_ctor_get(v_c_992_, 0);
                        crate::leanh::lean_inc(v_fvarId_1157_);
                        v_k_1158_ = crate::leanh::lean_ctor_get(v_c_992_, 3);
                        crate::leanh::lean_inc_ref(v_k_1158_);
                        crate::leanh::lean_dec_ref_known(v_c_992_, 4);
                        v___x_1159_ = l_Lean_instBEqFVarId_beq(v_fvarId_1157_, v_fvarId_991_);
                        crate::leanh::lean_dec(v_fvarId_1157_);
                        if v___x_1159_ == 0 {
                            v_c_992_ = v_k_1158_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_k_1158_);
                            v___x_1161_ = crate::leanh::lean_box((v___x_1159_) as usize);
                            v___x_1162_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1162_, 0, v___x_1161_);
                            crate::leanh::lean_ctor_set(v___x_1162_, 1, v_a_994_);
                            v___x_1163_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1163_, 0, v___x_1162_);
                            return v___x_1163_;
                        }
                    }
                    13 => {
                        v_fvarId_1164_ = crate::leanh::lean_ctor_get(v_c_992_, 0);
                        v_k_1165_ = crate::leanh::lean_ctor_get(v_c_992_, 1);
                        v_isSharedCheck_1176_ = (!crate::leanh::lean_is_exclusive(v_c_992_)) as u8;
                        if v_isSharedCheck_1176_ == 0 {
                            v___x_1167_ = v_c_992_;
                            v_isShared_1168_ = v_isSharedCheck_1176_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_k_1165_);
                            crate::leanh::lean_inc(v_fvarId_1164_);
                            crate::leanh::lean_dec(v_c_992_);
                            v___x_1167_ = crate::leanh::lean_box(0);
                            v_isShared_1168_ = v_isSharedCheck_1176_;
                            state = 16;
                            continue;
                        }
                    }
                    _ => {
                        v_fvarId_1177_ = crate::leanh::lean_ctor_get(v_c_992_, 0);
                        crate::leanh::lean_inc(v_fvarId_1177_);
                        v_k_1178_ = crate::leanh::lean_ctor_get(v_c_992_, 2);
                        crate::leanh::lean_inc_ref(v_k_1178_);
                        crate::leanh::lean_dec_ref(v_c_992_);
                        v___x_1179_ = l_Lean_instBEqFVarId_beq(v_fvarId_1177_, v_fvarId_991_);
                        crate::leanh::lean_dec(v_fvarId_1177_);
                        if v___x_1179_ == 0 {
                            v_c_992_ = v_k_1178_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_k_1178_);
                            v___x_1181_ = crate::leanh::lean_box((v___x_1179_) as usize);
                            v___x_1182_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1182_, 0, v___x_1181_);
                            crate::leanh::lean_ctor_set(v___x_1182_, 1, v_a_994_);
                            v___x_1183_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1183_, 0, v___x_1182_);
                            return v___x_1183_;
                        }
                    }
                }
            }
            1 => {
                v_targetSet_1005_ = crate::leanh::lean_ctor_get(v_a_993_, 0);
                v___x_1006_ = 1;
                v___x_1007_ =
                    l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(
                        v___x_1006_,
                        v_decl_1000_,
                        v_targetSet_1005_,
                    );
                crate::leanh::lean_dec_ref(v_decl_1000_);
                if v___x_1007_ == 0 {
                    crate::leanh::lean_del_object(v___x_1003_);
                    v_c_992_ = v_k_1001_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_k_1001_);
                    v___x_1009_ = crate::leanh::lean_box((v___x_1007_) as usize);
                    if v_isShared_1004_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1003_, 1, v_a_994_);
                        crate::leanh::lean_ctor_set(v___x_1003_, 0, v___x_1009_);
                        v___x_1011_ = v___x_1003_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1013_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1009_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_a_994_);
                        v___x_1011_ = v_reuseFailAlloc_1013_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1012_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1012_, 0, v___x_1011_);
                return v___x_1012_;
            }
            3 => {
                v___x_1058_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1059_ = lean_array_get_size(v_args_1028_);
                v___x_1060_ = lean_nat_dec_lt(v___x_1058_, v___x_1059_);
                if v___x_1060_ == 0 {
                    crate::leanh::lean_dec_ref(v_args_1028_);
                    v___y_1033_ = v___x_1060_;
                    state = 4;
                    continue;
                } else {
                    if v___x_1060_ == 0 {
                        crate::leanh::lean_dec_ref(v_args_1028_);
                        v___y_1033_ = v___x_1060_;
                        state = 4;
                        continue;
                    } else {
                        v___x_1061_ = 0usize;
                        v___x_1062_ = lean_usize_of_nat(v___x_1059_);
                        v___x_1063_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__3(v_a_993_, v_args_1028_, v___x_1061_, v___x_1062_);
                        crate::leanh::lean_dec_ref(v_args_1028_);
                        if v___x_1063_ == 0 {
                            v___y_1033_ = v___x_1063_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_1030_);
                            crate::leanh::lean_dec(v_fvarId_1027_);
                            v___x_1064_ = crate::leanh::lean_box((v___x_1063_) as usize);
                            v___x_1065_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1065_, 0, v___x_1064_);
                            crate::leanh::lean_ctor_set(v___x_1065_, 1, v_a_994_);
                            v___x_1066_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1066_, 0, v___x_1065_);
                            return v___x_1066_;
                        }
                    }
                }
            }
            4 => {
                v___x_1034_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_a_994_, v_fvarId_1027_);
                if v___x_1034_ == 0 {
                    crate::leanh::lean_del_object(v___x_1030_);
                    v___x_1035_ = 1;
                    v___x_1036_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(
                        v___x_1035_,
                        v_fvarId_1027_,
                        v_a_996_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1036_) == 0 {
                        v_a_1037_ = crate::leanh::lean_ctor_get(v___x_1036_, 0);
                        crate::leanh::lean_inc(v_a_1037_);
                        crate::leanh::lean_dec_ref_known(v___x_1036_, 1);
                        if crate::leanh::lean_obj_tag(v_a_1037_) == 1 {
                            v_val_1038_ = crate::leanh::lean_ctor_get(v_a_1037_, 0);
                            crate::leanh::lean_inc(v_val_1038_);
                            crate::leanh::lean_dec_ref_known(v_a_1037_, 1);
                            v_value_1039_ = crate::leanh::lean_ctor_get(v_val_1038_, 4);
                            crate::leanh::lean_inc_ref(v_value_1039_);
                            crate::leanh::lean_dec(v_val_1038_);
                            v___x_1040_ = crate::leanh::lean_box(0);
                            v___x_1041_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_a_994_, v_fvarId_1027_, v___x_1040_);
                            v_c_992_ = v_value_1039_;
                            v_a_994_ = v___x_1041_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_1037_);
                            crate::leanh::lean_dec(v_fvarId_1027_);
                            v___x_1043_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3_once), _init_l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___closed__3);
                            v___x_1044_ = l_panic___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__2(v___x_1043_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
                            return v___x_1044_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fvarId_1027_);
                        crate::leanh::lean_dec_ref(v_a_994_);
                        v_a_1045_ = crate::leanh::lean_ctor_get(v___x_1036_, 0);
                        v_isSharedCheck_1052_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1036_)) as u8;
                        if v_isSharedCheck_1052_ == 0 {
                            v___x_1047_ = v___x_1036_;
                            v_isShared_1048_ = v_isSharedCheck_1052_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1045_);
                            crate::leanh::lean_dec(v___x_1036_);
                            v___x_1047_ = crate::leanh::lean_box(0);
                            v_isShared_1048_ = v_isSharedCheck_1052_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fvarId_1027_);
                    v___x_1053_ = crate::leanh::lean_box((v___y_1033_) as usize);
                    if v_isShared_1031_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1030_, 0);
                        crate::leanh::lean_ctor_set(v___x_1030_, 1, v_a_994_);
                        crate::leanh::lean_ctor_set(v___x_1030_, 0, v___x_1053_);
                        v___x_1055_ = v___x_1030_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1057_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1053_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_a_994_);
                        v___x_1055_ = v_reuseFailAlloc_1057_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_1048_ == 0 {
                    v___x_1050_ = v___x_1047_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1051_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
                    v___x_1050_ = v_reuseFailAlloc_1051_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1050_;
            }
            7 => {
                v___x_1056_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1056_, 0, v___x_1055_);
                return v___x_1056_;
            }
            8 => {
                v_discr_1072_ = crate::leanh::lean_ctor_get(v_cases_1068_, 2);
                crate::leanh::lean_inc(v_discr_1072_);
                v_alts_1073_ = crate::leanh::lean_ctor_get(v_cases_1068_, 3);
                crate::leanh::lean_inc_ref(v_alts_1073_);
                crate::leanh::lean_dec_ref(v_cases_1068_);
                v___x_1074_ = l_Lean_instBEqFVarId_beq(v_discr_1072_, v_fvarId_991_);
                crate::leanh::lean_dec(v_discr_1072_);
                if v___x_1074_ == 0 {
                    v___x_1075_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1076_ = lean_array_get_size(v_alts_1073_);
                    v___x_1077_ = lean_nat_dec_lt(v___x_1075_, v___x_1076_);
                    if v___x_1077_ == 0 {
                        crate::leanh::lean_dec_ref(v_alts_1073_);
                        v___x_1078_ = crate::leanh::lean_box((v___x_1074_) as usize);
                        v___x_1079_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1079_, 0, v___x_1078_);
                        crate::leanh::lean_ctor_set(v___x_1079_, 1, v_a_994_);
                        if v_isShared_1071_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_1070_, 0);
                            crate::leanh::lean_ctor_set(v___x_1070_, 0, v___x_1079_);
                            v___x_1081_ = v___x_1070_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_1082_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
                            v___x_1081_ = v_reuseFailAlloc_1082_;
                            state = 9;
                            continue;
                        }
                    } else {
                        if v___x_1077_ == 0 {
                            crate::leanh::lean_dec_ref(v_alts_1073_);
                            v___x_1083_ = crate::leanh::lean_box((v___x_1074_) as usize);
                            v___x_1084_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1084_, 0, v___x_1083_);
                            crate::leanh::lean_ctor_set(v___x_1084_, 1, v_a_994_);
                            if v_isShared_1071_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_1070_, 0);
                                crate::leanh::lean_ctor_set(v___x_1070_, 0, v___x_1084_);
                                v___x_1086_ = v___x_1070_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_1087_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
                                v___x_1086_ = v_reuseFailAlloc_1087_;
                                state = 10;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1070_);
                            v___x_1088_ = 0usize;
                            v___x_1089_ = lean_usize_of_nat(v___x_1076_);
                            v___x_1090_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(v_fvarId_991_, v_alts_1073_, v___x_1088_, v___x_1089_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
                            crate::leanh::lean_dec_ref(v_alts_1073_);
                            return v___x_1090_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_alts_1073_);
                    v___x_1091_ = crate::leanh::lean_box((v___x_1074_) as usize);
                    v___x_1092_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1092_, 0, v___x_1091_);
                    crate::leanh::lean_ctor_set(v___x_1092_, 1, v_a_994_);
                    if v_isShared_1071_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1070_, 0);
                        crate::leanh::lean_ctor_set(v___x_1070_, 0, v___x_1092_);
                        v___x_1094_ = v___x_1070_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1095_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
                        v___x_1094_ = v_reuseFailAlloc_1095_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_1081_;
            }
            10 => {
                return v___x_1086_;
            }
            11 => {
                return v___x_1094_;
            }
            12 => {
                v___x_1101_ = l_Lean_instBEqFVarId_beq(v_fvarId_1097_, v_fvarId_991_);
                crate::leanh::lean_dec(v_fvarId_1097_);
                v___x_1102_ = crate::leanh::lean_box((v___x_1101_) as usize);
                v___x_1103_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1103_, 0, v___x_1102_);
                crate::leanh::lean_ctor_set(v___x_1103_, 1, v_a_994_);
                if v_isShared_1100_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1099_, 0);
                    crate::leanh::lean_ctor_set(v___x_1099_, 0, v___x_1103_);
                    v___x_1105_ = v___x_1099_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1106_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
                    v___x_1105_ = v_reuseFailAlloc_1106_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1105_;
            }
            14 => {
                v___x_1111_ = 0;
                v___x_1112_ = crate::leanh::lean_box((v___x_1111_) as usize);
                v___x_1113_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1113_, 0, v___x_1112_);
                crate::leanh::lean_ctor_set(v___x_1113_, 1, v_a_994_);
                if v_isShared_1110_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1109_, 0);
                    crate::leanh::lean_ctor_set(v___x_1109_, 0, v___x_1113_);
                    v___x_1115_ = v___x_1109_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1116_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
                    v___x_1115_ = v_reuseFailAlloc_1116_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1115_;
            }
            16 => {
                v___x_1169_ = l_Lean_instBEqFVarId_beq(v_fvarId_1164_, v_fvarId_991_);
                crate::leanh::lean_dec(v_fvarId_1164_);
                if v___x_1169_ == 0 {
                    crate::leanh::lean_del_object(v___x_1167_);
                    v_c_992_ = v_k_1165_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_k_1165_);
                    v___x_1171_ = crate::leanh::lean_box((v___x_1169_) as usize);
                    if v_isShared_1168_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1167_, 0);
                        crate::leanh::lean_ctor_set(v___x_1167_, 1, v_a_994_);
                        crate::leanh::lean_ctor_set(v___x_1167_, 0, v___x_1171_);
                        v___x_1173_ = v___x_1167_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_1175_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1171_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_a_994_);
                        v___x_1173_ = v_reuseFailAlloc_1175_;
                        state = 17;
                        continue;
                    }
                }
            }
            17 => {
                v___x_1174_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1174_, 0, v___x_1173_);
                return v___x_1174_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(
    mut v_fvarId_1184_: *mut crate::leanh::LeanObject,
    mut v_as_1185_: *mut crate::leanh::LeanObject,
    mut v_i_1186_: usize,
    mut v_stop_1187_: usize,
    mut v___y_1188_: *mut crate::leanh::LeanObject,
    mut v___y_1189_: *mut crate::leanh::LeanObject,
    mut v___y_1190_: *mut crate::leanh::LeanObject,
    mut v___y_1191_: *mut crate::leanh::LeanObject,
    mut v___y_1192_: *mut crate::leanh::LeanObject,
    mut v___y_1193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1195_: u8 = 0;
    let mut v___x_1196_: u8 = 0;
    let mut v___y_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1203_: u8 = 0;
    let mut v_fst_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: u8 = 0;
    let mut v_snd_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: usize = 0;
    let mut v___x_1208_: usize = 0;
    let mut v_snd_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1213_: u8 = 0;
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1221_: u8 = 0;
    let mut v_unused_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1223_: u8 = 0;
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: u8 = 0;
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1195_ = lean_usize_dec_eq(v_i_1186_, v_stop_1187_);
                if v___x_1195_ == 0 {
                    v___x_1196_ = 1;
                    v___x_1224_ = lean_array_uget_borrowed(v_as_1185_, v_i_1186_);
                    match crate::leanh::lean_obj_tag(v___x_1224_) {
                        0 => {
                            v_code_1225_ = crate::leanh::lean_ctor_get(v___x_1224_, 2);
                            crate::leanh::lean_inc_ref(v_code_1225_);
                            v___y_1198_ = v_code_1225_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_1226_ = crate::leanh::lean_ctor_get(v___x_1224_, 1);
                            crate::leanh::lean_inc_ref(v_code_1226_);
                            v___y_1198_ = v_code_1226_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_1227_ = crate::leanh::lean_ctor_get(v___x_1224_, 0);
                            crate::leanh::lean_inc_ref(v_code_1227_);
                            v___y_1198_ = v_code_1227_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_1228_ = 0;
                    v___x_1229_ = crate::leanh::lean_box((v___x_1228_) as usize);
                    v___x_1230_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1230_, 0, v___x_1229_);
                    crate::leanh::lean_ctor_set(v___x_1230_, 1, v___y_1189_);
                    v___x_1231_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1231_, 0, v___x_1230_);
                    return v___x_1231_;
                }
            }
            1 => {
                v___x_1199_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_1184_, v___y_1198_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
                if crate::leanh::lean_obj_tag(v___x_1199_) == 0 {
                    v_a_1200_ = crate::leanh::lean_ctor_get(v___x_1199_, 0);
                    v_isSharedCheck_1223_ = (!crate::leanh::lean_is_exclusive(v___x_1199_)) as u8;
                    if v_isSharedCheck_1223_ == 0 {
                        v___x_1202_ = v___x_1199_;
                        v_isShared_1203_ = v_isSharedCheck_1223_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1200_);
                        crate::leanh::lean_dec(v___x_1199_);
                        v___x_1202_ = crate::leanh::lean_box(0);
                        v_isShared_1203_ = v_isSharedCheck_1223_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_1199_;
                }
            }
            2 => {
                v_fst_1204_ = crate::leanh::lean_ctor_get(v_a_1200_, 0);
                v___x_1205_ = (crate::leanh::lean_unbox(v_fst_1204_) as u8);
                if v___x_1205_ == 0 {
                    crate::leanh::lean_del_object(v___x_1202_);
                    v_snd_1206_ = crate::leanh::lean_ctor_get(v_a_1200_, 1);
                    crate::leanh::lean_inc(v_snd_1206_);
                    crate::leanh::lean_dec(v_a_1200_);
                    v___x_1207_ = 1usize;
                    v___x_1208_ = lean_usize_add(v_i_1186_, v___x_1207_);
                    v_i_1186_ = v___x_1208_;
                    v___y_1189_ = v_snd_1206_;
                    state = 0;
                    continue;
                } else {
                    v_snd_1210_ = crate::leanh::lean_ctor_get(v_a_1200_, 1);
                    v_isSharedCheck_1221_ = (!crate::leanh::lean_is_exclusive(v_a_1200_)) as u8;
                    if v_isSharedCheck_1221_ == 0 {
                        v_unused_1222_ = crate::leanh::lean_ctor_get(v_a_1200_, 0);
                        crate::leanh::lean_dec(v_unused_1222_);
                        v___x_1212_ = v_a_1200_;
                        v_isShared_1213_ = v_isSharedCheck_1221_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1210_);
                        crate::leanh::lean_dec(v_a_1200_);
                        v___x_1212_ = crate::leanh::lean_box(0);
                        v_isShared_1213_ = v_isSharedCheck_1221_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1214_ = crate::leanh::lean_box((v___x_1196_) as usize);
                if v_isShared_1213_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1212_, 0, v___x_1214_);
                    v___x_1216_ = v___x_1212_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1220_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1214_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_snd_1210_);
                    v___x_1216_ = v_reuseFailAlloc_1220_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1203_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1202_, 0, v___x_1216_);
                    v___x_1218_ = v___x_1202_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1219_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
                    v___x_1218_ = v_reuseFailAlloc_1219_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1218_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4___boxed(
    mut v_fvarId_1232_: *mut crate::leanh::LeanObject,
    mut v_as_1233_: *mut crate::leanh::LeanObject,
    mut v_i_1234_: *mut crate::leanh::LeanObject,
    mut v_stop_1235_: *mut crate::leanh::LeanObject,
    mut v___y_1236_: *mut crate::leanh::LeanObject,
    mut v___y_1237_: *mut crate::leanh::LeanObject,
    mut v___y_1238_: *mut crate::leanh::LeanObject,
    mut v___y_1239_: *mut crate::leanh::LeanObject,
    mut v___y_1240_: *mut crate::leanh::LeanObject,
    mut v___y_1241_: *mut crate::leanh::LeanObject,
    mut v___y_1242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1243_: usize = 0;
    let mut v_stop_boxed_1244_: usize = 0;
    let mut v_res_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1243_ = crate::leanh::lean_unbox_usize(v_i_1234_);
    crate::leanh::lean_dec(v_i_1234_);
    v_stop_boxed_1244_ = crate::leanh::lean_unbox_usize(v_stop_1235_);
    crate::leanh::lean_dec(v_stop_1235_);
    v_res_1245_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__4(v_fvarId_1232_, v_as_1233_, v_i_boxed_1243_, v_stop_boxed_1244_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
    crate::leanh::lean_dec(v___y_1241_);
    crate::leanh::lean_dec_ref(v___y_1240_);
    crate::leanh::lean_dec(v___y_1239_);
    crate::leanh::lean_dec_ref(v___y_1238_);
    crate::leanh::lean_dec_ref(v___y_1236_);
    crate::leanh::lean_dec_ref(v_as_1233_);
    crate::leanh::lean_dec(v_fvarId_1232_);
    return v_res_1245_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go___boxed(
    mut v_fvarId_1246_: *mut crate::leanh::LeanObject,
    mut v_c_1247_: *mut crate::leanh::LeanObject,
    mut v_a_1248_: *mut crate::leanh::LeanObject,
    mut v_a_1249_: *mut crate::leanh::LeanObject,
    mut v_a_1250_: *mut crate::leanh::LeanObject,
    mut v_a_1251_: *mut crate::leanh::LeanObject,
    mut v_a_1252_: *mut crate::leanh::LeanObject,
    mut v_a_1253_: *mut crate::leanh::LeanObject,
    mut v_a_1254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1255_ =
        l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(
            v_fvarId_1246_,
            v_c_1247_,
            v_a_1248_,
            v_a_1249_,
            v_a_1250_,
            v_a_1251_,
            v_a_1252_,
            v_a_1253_,
        );
    crate::leanh::lean_dec(v_a_1253_);
    crate::leanh::lean_dec_ref(v_a_1252_);
    crate::leanh::lean_dec(v_a_1251_);
    crate::leanh::lean_dec_ref(v_a_1250_);
    crate::leanh::lean_dec_ref(v_a_1248_);
    crate::leanh::lean_dec(v_fvarId_1246_);
    return v_res_1255_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0(
    mut v_00_u03b2_1256_: *mut crate::leanh::LeanObject,
    mut v_m_1257_: *mut crate::leanh::LeanObject,
    mut v_a_1258_: *mut crate::leanh::LeanObject,
    mut v_b_1259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1260_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0___redArg(v_m_1257_, v_a_1258_, v_b_1259_);
    return v___x_1260_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1(
    mut v_00_u03b2_1261_: *mut crate::leanh::LeanObject,
    mut v_m_1262_: *mut crate::leanh::LeanObject,
    mut v_a_1263_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1264_: u8 = 0;
    v___x_1264_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___redArg(v_m_1262_, v_a_1263_);
    return v___x_1264_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1___boxed(
    mut v_00_u03b2_1265_: *mut crate::leanh::LeanObject,
    mut v_m_1266_: *mut crate::leanh::LeanObject,
    mut v_a_1267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1268_: u8 = 0;
    let mut v_r_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1268_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__1(v_00_u03b2_1265_, v_m_1266_, v_a_1267_);
    crate::leanh::lean_dec(v_a_1267_);
    crate::leanh::lean_dec_ref(v_m_1266_);
    v_r_1269_ = crate::leanh::lean_box((v_res_1268_) as usize);
    return v_r_1269_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0(
    mut v_00_u03b2_1270_: *mut crate::leanh::LeanObject,
    mut v_a_1271_: *mut crate::leanh::LeanObject,
    mut v_x_1272_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1273_: u8 = 0;
    v___x_1273_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___redArg(v_a_1271_, v_x_1272_);
    return v___x_1273_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_1274_: *mut crate::leanh::LeanObject,
    mut v_a_1275_: *mut crate::leanh::LeanObject,
    mut v_x_1276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1277_: u8 = 0;
    let mut v_r_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1277_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__0(v_00_u03b2_1274_, v_a_1275_, v_x_1276_);
    crate::leanh::lean_dec(v_x_1276_);
    crate::leanh::lean_dec(v_a_1275_);
    v_r_1278_ = crate::leanh::lean_box((v_res_1277_) as usize);
    return v_r_1278_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1(
    mut v_00_u03b2_1279_: *mut crate::leanh::LeanObject,
    mut v_data_1280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1281_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1___redArg(v_data_1280_);
    return v___x_1281_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3(
    mut v_00_u03b2_1282_: *mut crate::leanh::LeanObject,
    mut v_i_1283_: *mut crate::leanh::LeanObject,
    mut v_source_1284_: *mut crate::leanh::LeanObject,
    mut v_target_1285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1286_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3___redArg(v_i_1283_, v_source_1284_, v_target_1285_);
    return v___x_1286_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3_spec__7(
    mut v_00_u03b2_1287_: *mut crate::leanh::LeanObject,
    mut v_x_1288_: *mut crate::leanh::LeanObject,
    mut v_x_1289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1290_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go_spec__0_spec__1_spec__3_spec__7___redArg(v_x_1288_, v_x_1289_);
    return v___x_1290_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_isFVarLiveIn(
    mut v_c_1291_: *mut crate::leanh::LeanObject,
    mut v_fvarId_1292_: *mut crate::leanh::LeanObject,
    mut v_a_1293_: *mut crate::leanh::LeanObject,
    mut v_a_1294_: *mut crate::leanh::LeanObject,
    mut v_a_1295_: *mut crate::leanh::LeanObject,
    mut v_a_1296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1305_: u8 = 0;
    let mut v_fst_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1310_: u8 = 0;
    let mut v_a_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1314_: u8 = 0;
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1318_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1298_ = l_Lean_instEmptyCollectionFVarIdHashSet;
                crate::leanh::lean_inc_n(v_fvarId_1292_, 2);
                v___x_1299_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_fvarId_1292_);
                v___x_1300_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1300_, 0, v___x_1299_);
                crate::leanh::lean_ctor_set(v___x_1300_, 1, v_fvarId_1292_);
                v___x_1301_ = l___private_Lean_Compiler_LCNF_LiveVars_0__Lean_Compiler_LCNF_Code_isFVarLiveIn_go(v_fvarId_1292_, v_c_1291_, v___x_1300_, v___x_1298_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
                crate::leanh::lean_dec_ref_known(v___x_1300_, 2);
                crate::leanh::lean_dec(v_fvarId_1292_);
                if crate::leanh::lean_obj_tag(v___x_1301_) == 0 {
                    v_a_1302_ = crate::leanh::lean_ctor_get(v___x_1301_, 0);
                    v_isSharedCheck_1310_ = (!crate::leanh::lean_is_exclusive(v___x_1301_)) as u8;
                    if v_isSharedCheck_1310_ == 0 {
                        v___x_1304_ = v___x_1301_;
                        v_isShared_1305_ = v_isSharedCheck_1310_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1302_);
                        crate::leanh::lean_dec(v___x_1301_);
                        v___x_1304_ = crate::leanh::lean_box(0);
                        v_isShared_1305_ = v_isSharedCheck_1310_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1311_ = crate::leanh::lean_ctor_get(v___x_1301_, 0);
                    v_isSharedCheck_1318_ = (!crate::leanh::lean_is_exclusive(v___x_1301_)) as u8;
                    if v_isSharedCheck_1318_ == 0 {
                        v___x_1313_ = v___x_1301_;
                        v_isShared_1314_ = v_isSharedCheck_1318_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1311_);
                        crate::leanh::lean_dec(v___x_1301_);
                        v___x_1313_ = crate::leanh::lean_box(0);
                        v_isShared_1314_ = v_isSharedCheck_1318_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1306_ = crate::leanh::lean_ctor_get(v_a_1302_, 0);
                crate::leanh::lean_inc(v_fst_1306_);
                crate::leanh::lean_dec(v_a_1302_);
                if v_isShared_1305_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1304_, 0, v_fst_1306_);
                    v___x_1308_ = v___x_1304_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1309_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_fst_1306_);
                    v___x_1308_ = v_reuseFailAlloc_1309_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1308_;
            }
            3 => {
                if v_isShared_1314_ == 0 {
                    v___x_1316_ = v___x_1313_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1317_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
                    v___x_1316_ = v_reuseFailAlloc_1317_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1316_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_isFVarLiveIn___boxed(
    mut v_c_1319_: *mut crate::leanh::LeanObject,
    mut v_fvarId_1320_: *mut crate::leanh::LeanObject,
    mut v_a_1321_: *mut crate::leanh::LeanObject,
    mut v_a_1322_: *mut crate::leanh::LeanObject,
    mut v_a_1323_: *mut crate::leanh::LeanObject,
    mut v_a_1324_: *mut crate::leanh::LeanObject,
    mut v_a_1325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1326_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(
        v_c_1319_,
        v_fvarId_1320_,
        v_a_1321_,
        v_a_1322_,
        v_a_1323_,
        v_a_1324_,
    );
    crate::leanh::lean_dec(v_a_1324_);
    crate::leanh::lean_dec_ref(v_a_1323_);
    crate::leanh::lean_dec(v_a_1322_);
    crate::leanh::lean_dec_ref(v_a_1321_);
    return v_res_1326_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_LiveVars(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_DependsOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_LiveVars(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_LiveVars(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_DependsOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_LiveVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_LiveVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_LiveVars(builtin);
}
