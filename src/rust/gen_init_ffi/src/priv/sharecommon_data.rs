use std::hash::Hasher;

use leanh_l1::datatypes::LeanObject;

#[derive(Default)]
pub struct IdentityHasher(u64);

impl Hasher for IdentityHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        let mut h = 0u64;
        let mut shift = 0;
        for &byte in bytes.iter().take(8) {
            h |= (byte as u64) << shift;
            shift += 8;
        }
        self.0 = h;
    }

    fn write_usize(&mut self, i: usize) {
        self.0 = i as u64;
    }

    fn write_u64(&mut self, i: u64) {
        self.0 = i;
    }
}

// Helper for lean_state_sharecommon logic (non-quick stateful)
pub struct ShareCommonState {
    pub map_find: *mut LeanObject,
    pub map_insert: *mut LeanObject,
    pub set_find: *mut LeanObject,
    pub set_insert: *mut LeanObject,
    pub map: *mut LeanObject,
    pub set: *mut LeanObject,
}

pub struct ShareCommonFn {
    pub state: ShareCommonState,
    pub children: Vec<*mut LeanObject>,
    pub todo: Vec<*mut LeanObject>,
}
