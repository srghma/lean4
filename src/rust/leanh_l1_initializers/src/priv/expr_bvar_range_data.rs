const EXPR_BVAR_RANGE_SHIFT: u32 = 44;
const EXPR_BVAR_RANGE_MASK: u64 = 0xFFFFF;

#[inline]
pub unsafe fn expr_bvar_range_data(data: u64) -> u64 {
    (data >> EXPR_BVAR_RANGE_SHIFT) & EXPR_BVAR_RANGE_MASK
}
