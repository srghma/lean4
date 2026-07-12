use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_ctor_get_uint64::lean_ctor_get_uint64, lean_is_scalar::lean_is_scalar,
        lean_obj_tag::lean_obj_tag,
    },
};

#[repr(u8)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum LeanLevelTag {
    Succ = 1,
    Max = 2,
    IMax = 3,
    Param = 4,
    MVar = 5,
}

impl LeanLevelTag {
    #[inline]
    pub fn from_u8(tag: u8) -> Self {
        match tag {
            1 => LeanLevelTag::Succ,
            2 => LeanLevelTag::Max,
            3 => LeanLevelTag::IMax,
            4 => LeanLevelTag::Param,
            5 => LeanLevelTag::MVar,
            n => panic!("invalid LeanLevelTag {n}"),
        }
    }
}

#[inline]
unsafe fn lean_level_tag(level: *const LeanObject) -> LeanLevelTag {
    LeanLevelTag::from_u8(lean_obj_tag(level))
}

#[inline]
pub unsafe fn level_data(level: *const LeanObject) -> u64 {
    if lean_is_scalar(level) {
        return 2221u64;
    }
    let num_fields = match lean_level_tag(level) {
        LeanLevelTag::Succ | LeanLevelTag::Param | LeanLevelTag::MVar => 1,
        LeanLevelTag::Max | LeanLevelTag::IMax => 2,
    };
    lean_ctor_get_uint64(
        level,
        (core::mem::size_of::<*mut LeanObject>() * num_fields) as u32,
    )
}
