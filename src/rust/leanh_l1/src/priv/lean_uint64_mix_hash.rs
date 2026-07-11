#[inline]
pub fn lean_uint64_mix_hash(h: u64, k: u64) -> u64 {
    const M: u64 = 0xc6a4a7935bd1e995u64;
    const R: u32 = 47;
    let mut h: u64 = h ^ k.wrapping_mul(M);
    let mut k: u64 = k;
    k = k.wrapping_mul(M);
    k ^= k >> R;
    k = k.wrapping_mul(M);
    h ^= k;
    h = h.wrapping_mul(M);
    h ^= h >> R;
    h = h.wrapping_mul(M);
    h ^= h >> R;
    h
}
