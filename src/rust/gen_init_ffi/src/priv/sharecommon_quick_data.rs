use leanh_l1::datatypes::LeanObject;
use std::{
    collections::{HashMap, HashSet},
    hash::BuildHasherDefault,
};

use crate::r#priv::sharecommon_data::IdentityHasher;

pub type LeanHashBuilder = BuildHasherDefault<IdentityHasher>;
pub type ShareCache = HashMap<usize, usize, LeanHashBuilder>;

#[derive(Clone, Copy, Eq, PartialEq, Hash)]
pub struct ShareConsNode(pub *mut LeanObject);

// impl Eq for ShareConsNode {}
// impl PartialEq for ShareConsNode {
//     fn eq(&self, other: &Self) -> bool {
//         unsafe { lean_sharecommon_eq(self.0, other.0) }
//     }
// }
// impl std::hash::Hash for ShareConsNode {
//     fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
//         let h = unsafe { lean_sharecommon_hash(self.0) };
//         state.write_u64(h);
//     }
// }

pub type ShareSet = HashSet<ShareConsNode, LeanHashBuilder>;

// Now, sharecommon_quick_fn state
pub struct RustShareCommonQuick {
    pub(crate) cache: ShareCache,
    pub(crate) set: ShareSet,
    pub(crate) check_set: bool,
}
