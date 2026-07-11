// ── UTF-8 decode helper ──────────────────────────────────────────────────────

#[inline]
pub(crate) unsafe fn string_utf8_get_core(str: *const u8, size: usize, i: usize) -> Option<u32> {
    let c = *str.add(i) as u32;
    if (c & 0x80) == 0 {
        return Some(c);
    }
    if (c & 0xe0) == 0xc0 && i + 1 < size {
        let c1 = *str.add(i + 1) as u32;
        let r = ((c & 0x1f) << 6) | (c1 & 0x3f);
        if r >= 0x80 {
            return Some(r);
        }
    }
    if (c & 0xf0) == 0xe0 && i + 2 < size {
        let c1 = *str.add(i + 1) as u32;
        let c2 = *str.add(i + 2) as u32;
        let r = ((c & 0x0f) << 12) | ((c1 & 0x3f) << 6) | (c2 & 0x3f);
        if r >= 0x800 && !(0xD800..=0xDFFF).contains(&r) {
            return Some(r);
        }
    }
    if (c & 0xf8) == 0xf0 && i + 3 < size {
        let c1 = *str.add(i + 1) as u32;
        let c2 = *str.add(i + 2) as u32;
        let c3 = *str.add(i + 3) as u32;
        let r = ((c & 0x07) << 18) | ((c1 & 0x3f) << 12) | ((c2 & 0x3f) << 6) | (c3 & 0x3f);
        if (0x10000..=0x10FFFF).contains(&r) {
            return Some(r);
        }
    }
    None
}
