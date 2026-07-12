pub use crate::datatypes::LeanTaskState;
use crate::datatypes::LeanObject;
use crate::{lean_ctor_get_uint8, lean_ctor_get_uint64, lean_is_scalar, lean_ptr_tag, lean_unbox};
use core::ffi::c_int;
pub use leanh_l1_initializers::todo_import_from_lean::lean_expr_mk_const::level_data;

#[repr(u32)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LeanExprKind {
    BVar = 0,
    FVar = 1,
    MVar = 2,
    Sort = 3,
    Const = 4,
    App = 5,
    Lambda = 6,
    Pi = 7,
    Let = 8,
    Lit = 9,
    MData = 10,
    Proj = 11,
}

impl LeanExprKind {
    #[inline(always)]
    pub fn from_u8(tag: u8) -> Self {
        match tag {
            0 => LeanExprKind::BVar,
            1 => LeanExprKind::FVar,
            2 => LeanExprKind::MVar,
            3 => LeanExprKind::Sort,
            4 => LeanExprKind::Const,
            5 => LeanExprKind::App,
            6 => LeanExprKind::Lambda,
            7 => LeanExprKind::Pi,
            8 => LeanExprKind::Let,
            9 => LeanExprKind::Lit,
            10 => LeanExprKind::MData,
            11 => LeanExprKind::Proj,
            n => panic!("invalid LeanExprKind tag {n}"),
        }
    }
}

impl PartialEq<u32> for LeanExprKind {
    fn eq(&self, other: &u32) -> bool {
        (*self as u32) == *other
    }
}

impl PartialEq<LeanExprKind> for u32 {
    fn eq(&self, other: &LeanExprKind) -> bool {
        *self == (*other as u32)
    }
}

#[repr(u32)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LeanLevelKind {
    Zero = 0,
    Succ = 1,
    Max = 2,
    IMax = 3,
    Param = 4,
    MVar = 5,
}

impl LeanLevelKind {
    #[inline(always)]
    pub fn from_u8(tag: u8) -> Self {
        match tag {
            0 => LeanLevelKind::Zero,
            1 => LeanLevelKind::Succ,
            2 => LeanLevelKind::Max,
            3 => LeanLevelKind::IMax,
            4 => LeanLevelKind::Param,
            5 => LeanLevelKind::MVar,
            n => panic!("invalid LeanLevelKind tag {n}"),
        }
    }
}

impl PartialEq<u32> for LeanLevelKind {
    fn eq(&self, other: &u32) -> bool {
        (*self as u32) == *other
    }
}

impl PartialEq<LeanLevelKind> for u32 {
    fn eq(&self, other: &LeanLevelKind) -> bool {
        *self == (*other as u32)
    }
}

#[repr(u8)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LeanBinderInfo {
    Default = 0,
    Implicit = 1,
    StrictImplicit = 2,
    InstImplicit = 3,
}

impl LeanBinderInfo {
    #[inline(always)]
    pub fn from_u8(tag: u8) -> Self {
        match tag {
            0 => LeanBinderInfo::Default,
            1 => LeanBinderInfo::Implicit,
            2 => LeanBinderInfo::StrictImplicit,
            3 => LeanBinderInfo::InstImplicit,
            n => panic!("invalid LeanBinderInfo tag {n}"),
        }
    }
}

#[inline(always)]
pub fn lean_binder_info_is_explicit(bi: LeanBinderInfo) -> bool {
    matches!(bi, LeanBinderInfo::Default)
}

#[repr(u32)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LeanNameTag {
    Anonymous = 0,
    String = 1,
    Numeral = 2,
}

#[inline(always)]
pub unsafe fn lean_name_tag(n: *const LeanObject) -> LeanNameTag {
    LeanNameTag::from_u8(lean_ptr_tag(n))
}

#[repr(u8)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LeanLiteralTag {
    Nat = 0,
    String = 1,
}

impl LeanLiteralTag {
    #[inline(always)]
    pub fn from_u8(tag: u8) -> Self {
        match tag {
            0 => LeanLiteralTag::Nat,
            1 => LeanLiteralTag::String,
            n => panic!("invalid LeanLiteralTag {n}"),
        }
    }
}

#[inline(always)]
pub unsafe fn lean_literal_tag(lit: *const LeanObject) -> LeanLiteralTag {
    LeanLiteralTag::from_u8(lean_ptr_tag(lit))
}

#[repr(u8)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LeanDataValueKind {
    Bool = 1,
    Name = 2,
    Nat = 3,
    String = 4,
}

impl LeanDataValueKind {
    #[inline(always)]
    pub fn from_u8(tag: u8) -> Self {
        match tag {
            0 => LeanDataValueKind::String,
            1 => LeanDataValueKind::Bool,
            2 => LeanDataValueKind::Name,
            3 => LeanDataValueKind::Nat,
            n => panic!("invalid LeanDataValueKind tag {n}"),
        }
    }
}

#[inline(always)]
pub unsafe fn lean_data_value_kind(dv: *const LeanObject) -> LeanDataValueKind {
    LeanDataValueKind::from_u8(lean_ptr_tag(dv))
}

#[repr(u32)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LeanConstantInfoTag {
    Axiom = 0,
    Definition = 1,
    Theorem = 2,
    Opaque = 3,
    Quot = 4,
    Inductive = 5,
    Constructor = 6,
    Recursor = 7,
}

impl LeanConstantInfoTag {
    #[inline(always)]
    pub fn from_u8(tag: u8) -> Self {
        match tag {
            0 => LeanConstantInfoTag::Axiom,
            1 => LeanConstantInfoTag::Definition,
            2 => LeanConstantInfoTag::Theorem,
            3 => LeanConstantInfoTag::Opaque,
            4 => LeanConstantInfoTag::Quot,
            5 => LeanConstantInfoTag::Inductive,
            6 => LeanConstantInfoTag::Constructor,
            7 => LeanConstantInfoTag::Recursor,
            n => panic!("invalid LeanConstantInfoTag {n}"),
        }
    }
}

#[inline(always)]
pub unsafe fn lean_constant_info_tag(info: *const LeanObject) -> LeanConstantInfoTag {
    LeanConstantInfoTag::from_u8(lean_ptr_tag(info))
}

#[repr(u32)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LeanReducibilityHintsTag {
    Opaque = 0,
    Abbreviation = 1,
    Regular = 2,
}

impl LeanReducibilityHintsTag {
    #[inline(always)]
    pub fn from_u8(tag: u8) -> Self {
        match tag {
            0 => LeanReducibilityHintsTag::Opaque,
            1 => LeanReducibilityHintsTag::Abbreviation,
            2 => LeanReducibilityHintsTag::Regular,
            n => panic!("invalid LeanReducibilityHintsTag {n}"),
        }
    }
}

#[inline(always)]
pub unsafe fn lean_reducibility_hints_tag(h: *const LeanObject) -> LeanReducibilityHintsTag {
    if lean_is_scalar(h) {
        LeanReducibilityHintsTag::from_u8(lean_unbox(h) as u8)
    } else {
        LeanReducibilityHintsTag::from_u8(lean_ptr_tag(h))
    }
}

#[repr(u8)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LeanIpAddrTag {
    V4 = 0,
    V6 = 1,
}

impl LeanIpAddrTag {
    #[inline(always)]
    pub fn from_u8(tag: u8) -> Self {
        match tag {
            0 => LeanIpAddrTag::V4,
            1 => LeanIpAddrTag::V6,
            n => panic!("invalid LeanIpAddrTag {n}"),
        }
    }
}

#[inline(always)]
pub unsafe fn lean_ip_addr_tag(ip_addr: *const LeanObject) -> LeanIpAddrTag {
    LeanIpAddrTag::from_u8(lean_ptr_tag(ip_addr))
}

#[repr(u8)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LeanLocalDeclTag {
    CDecl = 0,
    LDecl = 1,
}

impl LeanLocalDeclTag {
    #[inline(always)]
    pub fn from_u8(tag: u8) -> Self {
        match tag {
            0 => LeanLocalDeclTag::CDecl,
            1 => LeanLocalDeclTag::LDecl,
            n => panic!("invalid LeanLocalDeclTag {n}"),
        }
    }
}

#[inline(always)]
pub unsafe fn lean_local_decl_tag(d: *const LeanObject) -> LeanLocalDeclTag {
    LeanLocalDeclTag::from_u8(lean_ptr_tag(d))
}

#[repr(u32)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LeanMapEntryKind {
    Entries = 0,
    Node = 1,
}

impl LeanMapEntryKind {
    #[inline(always)]
    pub fn from_u8(tag: u8) -> Self {
        match tag {
            0 => LeanMapEntryKind::Entries,
            1 => LeanMapEntryKind::Node,
            n => panic!("invalid LeanMapEntryKind tag {n}"),
        }
    }
}

#[inline(always)]
pub unsafe fn lean_map_entry_kind(e: *const LeanObject) -> LeanMapEntryKind {
    LeanMapEntryKind::from_u8(lean_obj_tag(e))
}

#[repr(u32)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LeanMapNodeKind {
    Entries = 0,
    Collision = 1,
}

impl LeanMapNodeKind {
    #[inline(always)]
    pub fn from_u8(tag: u8) -> Self {
        match tag {
            0 => LeanMapNodeKind::Entries,
            1 => LeanMapNodeKind::Collision,
            n => panic!("invalid LeanMapNodeKind tag {n}"),
        }
    }
}

#[inline(always)]
pub unsafe fn lean_map_node_kind(n: *const LeanObject) -> LeanMapNodeKind {
    LeanMapNodeKind::from_u8(lean_ptr_tag(n))
}

#[repr(u32)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LeanExceptTag {
    Error = 0,
    Ok = 1,
}

impl LeanExceptTag {
    #[inline(always)]
    pub fn from_u8(tag: u8) -> Self {
        match tag {
            0 => LeanExceptTag::Error,
            1 => LeanExceptTag::Ok,
            n => panic!("invalid LeanExceptTag {n}"),
        }
    }
}

#[inline(always)]
pub unsafe fn lean_except_tag(o: *const LeanObject) -> LeanExceptTag {
    LeanExceptTag::from_u8(lean_ptr_tag(o))
}
pub const LEVEL_DATA_HAS_MVAR: u64 = 1 << 32;
pub const LEVEL_DATA_HAS_PARAM_BIT: u64 = 1u64 << 33;
pub const LEVEL_DATA_DEPTH_SHIFT: u32 = 40;
pub const EXPR_DATA_HAS_LEVEL_PARAM_BIT: u64 = 1u64 << 43;

// Socket address string buffer sizes shared by net helpers.
pub const INET_ADDRSTRLEN: usize = 16;
pub const INET6_ADDRSTRLEN: usize = 46;

// Object/file-layout constants shared by module/compact/process helpers.
pub const PTR_SIZE: usize = core::mem::size_of::<usize>();
pub const OLEAN_HEADER_SIZE: usize = 88;
pub const OLEAN_MARKER: &[u8; 5] = b"olean";
pub const OLEAN_VERSION_V2: u8 = 2;
pub const OLEAN_VERSION_V3: u8 = 3;
pub const OLEAN_FLAGS_GMP: u8 = 0b1;
pub const LEAN_MP_LIMB_SIZE: usize = 8;
pub const LEAN_MPZ_MP_D_OFFSET: usize = 16;
pub const LEAN_MPZ_MP_SIZE_OFFSET: usize = 12;
#[repr(u8)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LeanDefinitionSafety {
    Unsafe = 0,
    Safe = 1,
    Partial = 2,
}

pub const UV_EALREADY: c_int = -3003;

#[derive(Clone, Debug)]
pub struct LibInfo {
    pub base_addr: usize,
    pub id: std::string::String,
}

/// Round `d` up to the next multiple of PTR_SIZE.
#[inline(always)]
pub fn align_up_ptr(d: usize) -> usize {
    let rem = d % PTR_SIZE;
    if rem != 0 { d + PTR_SIZE - rem } else { d }
}

// Expr.Data helpers.
#[inline(always)]
pub unsafe fn expr_data(e: *const LeanObject) -> u64 {
    let num_objs = (*e).other as usize;
    lean_ctor_get_uint64(e, num_objs * core::mem::size_of::<*mut LeanObject>())
}

/// bvarRange = bits [63:44] of Expr.Data.
#[inline(always)]
pub unsafe fn expr_bvar_range_data(data: u64) -> u64 {
    data >> EXPR_BVAR_RANGE_SHIFT
}

/// bvarRange = bits [63:44] of Expr.Data.
#[inline(always)]
pub unsafe fn expr_bvar_range(e: *const LeanObject) -> u64 {
    expr_bvar_range_data(expr_data(e))
}

/// BinderInfo byte for Lambda/Pi.
#[inline(always)]
pub unsafe fn expr_binder_info_raw(e: *const LeanObject) -> LeanBinderInfo {
    let num_objs = (*e).other as usize;
    LeanBinderInfo::from_u8(lean_ctor_get_uint8(e, num_objs * 8 + 8))
}

#[inline(always)]
pub unsafe fn expr_kind(e: *const LeanObject) -> LeanExprKind {
    LeanExprKind::from_u8(lean_ptr_tag(e))
}

#[inline(always)]
pub unsafe fn level_kind(l: *const LeanObject) -> LeanLevelKind {
    if lean_is_scalar(l) {
        LeanLevelKind::Zero
    } else {
        LeanLevelKind::from_u8(lean_ptr_tag(l))
    }
}

/// nondep byte for Let.
#[inline(always)]
pub unsafe fn expr_let_nondep(e: *const LeanObject) -> bool {
    lean_ctor_get_uint8(e, 4 * 8 + 8) != 0
}
