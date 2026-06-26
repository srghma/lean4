/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use crate::*;

type MpnDigit = u32;
type MpnDoubleDigit = u64;

const DIGIT_BITS: usize = core::mem::size_of::<MpnDigit>() * 8;
const BASE: MpnDoubleDigit = 1u64 << DIGIT_BITS;

fn trim_size(digits: &[MpnDigit]) -> usize {
    let mut size = digits.len();
    while size > 1 && digits[size - 1] == 0 {
        size -= 1;
    }
    size
}

unsafe fn digit_slice<'a>(digits: *const MpnDigit, len: usize) -> &'a [MpnDigit] {
    core::slice::from_raw_parts(digits, len)
}

unsafe fn digit_slice_mut<'a>(digits: *mut MpnDigit, len: usize) -> &'a mut [MpnDigit] {
    core::slice::from_raw_parts_mut(digits, len)
}

fn mpn_compare_impl(a: &[MpnDigit], b: &[MpnDigit]) -> c_int {
    let len = a.len().max(b.len());
    for index in (0..len).rev() {
        let lhs = a.get(index).copied().unwrap_or(0);
        let rhs = b.get(index).copied().unwrap_or(0);
        if lhs > rhs {
            return 1;
        }
        if lhs < rhs {
            return -1;
        }
    }
    0
}

fn mpn_add_impl(a: &[MpnDigit], b: &[MpnDigit], c: &mut [MpnDigit]) -> usize {
    let len = a.len().max(b.len());
    let mut carry: MpnDigit = 0;
    for index in 0..len {
        let lhs = a.get(index).copied().unwrap_or(0);
        let rhs = b.get(index).copied().unwrap_or(0);
        let (sum, carry1) = lhs.overflowing_add(rhs);
        let (sum, carry2) = sum.overflowing_add(carry);
        c[index] = sum;
        carry = (carry1 || carry2) as MpnDigit;
    }
    c[len] = carry;
    trim_size(&c[..len + 1])
}

fn mpn_sub_impl(a: &[MpnDigit], b: &[MpnDigit], c: &mut [MpnDigit]) -> MpnDigit {
    let len = a.len().max(b.len());
    let mut borrow: MpnDigit = 0;
    for index in 0..len {
        let lhs = a.get(index).copied().unwrap_or(0);
        let rhs = b.get(index).copied().unwrap_or(0);
        let (diff, borrow1) = lhs.overflowing_sub(rhs);
        let (diff, borrow2) = diff.overflowing_sub(borrow);
        c[index] = diff;
        borrow = (borrow1 || borrow2) as MpnDigit;
    }
    borrow
}

fn mpn_mul_impl(a: &[MpnDigit], b: &[MpnDigit], c: &mut [MpnDigit]) {
    for value in c.iter_mut() {
        *value = 0;
    }
    for (j, rhs) in b.iter().copied().enumerate() {
        if rhs == 0 {
            c[j + a.len()] = 0;
            continue;
        }
        let mut carry: MpnDigit = 0;
        for (i, lhs) in a.iter().copied().enumerate() {
            let t = lhs as MpnDoubleDigit * rhs as MpnDoubleDigit
                + c[i + j] as MpnDoubleDigit
                + carry as MpnDoubleDigit;
            c[i + j] = t as MpnDigit;
            carry = (t >> DIGIT_BITS) as MpnDigit;
        }
        c[j + a.len()] = carry;
    }
}

fn first_bits(n: usize, x: MpnDigit) -> MpnDigit {
    x >> (DIGIT_BITS - n)
}

fn last_bits(n: usize, x: MpnDigit) -> MpnDigit {
    (x << (DIGIT_BITS - n)) >> (DIGIT_BITS - n)
}

fn div_normalize(numer: &[MpnDigit], denom: &[MpnDigit]) -> (usize, Vec<MpnDigit>, Vec<MpnDigit>) {
    let mut shift = 0usize;
    while !denom.is_empty() && ((denom[denom.len() - 1] << shift) & (1u32 << 31)) == 0 {
        shift += 1;
    }

    let mut n_numer = vec![0; numer.len() + 1];
    let mut n_denom = vec![0; denom.len()];

    if shift == 0 {
        n_numer[numer.len()] = 0;
        n_numer[..numer.len()].copy_from_slice(numer);
        n_denom.copy_from_slice(denom);
    } else if !numer.is_empty() {
        let last = numer.len() - 1;
        n_numer[numer.len()] = first_bits(shift, numer[last]);
        for index in (1..numer.len()).rev() {
            n_numer[index] = (numer[index] << shift) | first_bits(shift, numer[index - 1]);
        }
        n_numer[0] = numer[0] << shift;

        for index in (1..denom.len()).rev() {
            n_denom[index] = (denom[index] << shift) | first_bits(shift, denom[index - 1]);
        }
        n_denom[0] = denom[0] << shift;
    } else {
        shift = 0;
    }

    (shift, n_numer, n_denom)
}

fn div_unnormalize(numer: &[MpnDigit], denom_len: usize, shift: usize, rem: &mut [MpnDigit]) {
    if shift == 0 {
        rem[..denom_len].copy_from_slice(&numer[..denom_len]);
    } else {
        for index in 0..denom_len - 1 {
            rem[index] = (numer[index] >> shift)
                | (last_bits(shift, numer[index + 1]) << (DIGIT_BITS - shift));
        }
        rem[denom_len - 1] = numer[denom_len - 1] >> shift;
    }
}

fn div_1(numer: &mut [MpnDigit], denom: MpnDigit, quot: &mut [MpnDigit]) {
    for index in (1..numer.len()).rev() {
        let temp =
            ((numer[index] as MpnDoubleDigit) << DIGIT_BITS) | numer[index - 1] as MpnDoubleDigit;
        let q_hat = temp / denom as MpnDoubleDigit;
        let ms = temp - q_hat * denom as MpnDoubleDigit;
        let borrow = ms > temp;
        numer[index - 1] = ms as MpnDigit;
        numer[index] = (ms >> DIGIT_BITS) as MpnDigit;
        quot[index - 1] = q_hat as MpnDigit;
        if borrow {
            quot[index - 1] -= 1;
            numer[index] = numer[index - 1].wrapping_add(denom);
        }
    }
}

fn div_n(numer: &mut [MpnDigit], denom: &[MpnDigit], quot: &mut [MpnDigit]) {
    let m = numer.len() - denom.len();
    let n = denom.len();
    let mut ms = vec![0; n + 1];

    for j in (0..m).rev() {
        let temp =
            ((numer[j + n] as MpnDoubleDigit) << DIGIT_BITS) | numer[j + n - 1] as MpnDoubleDigit;
        let mut q_hat = temp / denom[n - 1] as MpnDoubleDigit;
        let mut r_hat = temp % denom[n - 1] as MpnDoubleDigit;
        while q_hat >= BASE
            || q_hat * denom[n - 2] as MpnDoubleDigit
                > (r_hat << DIGIT_BITS) + numer[j + n - 2] as MpnDoubleDigit
        {
            q_hat -= 1;
            r_hat += denom[n - 1] as MpnDoubleDigit;
            if r_hat >= BASE {
                break;
            }
        }

        let q_hat_small = q_hat as MpnDigit;
        mpn_mul_impl(&[q_hat_small], denom, &mut ms);
        let borrow = {
            let target = &mut numer[j..j + n + 1];
            mpn_sub_impl(&target.to_vec(), &ms, target)
        };
        quot[j] = q_hat_small;
        if borrow != 0 {
            quot[j] -= 1;
            let mut ab = vec![0; n + 2];
            mpn_add_impl(denom, &numer[j..j + n + 1].to_vec(), &mut ab);
            numer[j..j + n + 1].copy_from_slice(&ab[..n + 1]);
        }
    }
}

fn mpn_div_impl(
    numer: &[MpnDigit],
    denom: &[MpnDigit],
    quot: &mut [MpnDigit],
    rem: &mut [MpnDigit],
) {
    if numer.len() < denom.len() {
        for value in quot.iter_mut() {
            *value = 0;
        }
        for index in 0..denom.len() {
            rem[index] = numer.get(index).copied().unwrap_or(0);
        }
        return;
    }

    if numer.len() == 1 && denom.len() == 1 {
        quot[0] = numer[0] / denom[0];
        rem[0] = numer[0] % denom[0];
    } else if numer.len() == denom.len() && numer[numer.len() - 1] < denom[denom.len() - 1] {
        quot[0] = 0;
        for index in 0..denom.len() {
            rem[index] = numer.get(index).copied().unwrap_or(0);
        }
    } else {
        let (shift, mut u, v) = div_normalize(numer, denom);
        if denom.len() == 1 {
            div_1(&mut u, v[0], quot);
        } else {
            div_n(&mut u, &v, quot);
        }
        div_unnormalize(&u, v.len(), shift, rem);
    }
}

pub unsafe fn mpn_compare(
    a: *const MpnDigit,
    lnga: usize,
    b: *const MpnDigit,
    lngb: usize,
) -> c_int {
    mpn_compare_impl(digit_slice(a, lnga), digit_slice(b, lngb))
}

pub unsafe fn mpn_add(
    a: *const MpnDigit,
    lnga: usize,
    b: *const MpnDigit,
    lngb: usize,
    c: *mut MpnDigit,
    lngc_alloc: usize,
    plngc: *mut usize,
) {
    let lhs = digit_slice(a, lnga).to_vec();
    let rhs = digit_slice(b, lngb).to_vec();
    let size = mpn_add_impl(&lhs, &rhs, digit_slice_mut(c, lngc_alloc));
    *plngc = size;
}

pub unsafe fn mpn_sub(
    a: *const MpnDigit,
    lnga: usize,
    b: *const MpnDigit,
    lngb: usize,
    c: *mut MpnDigit,
    pborrow: *mut MpnDigit,
) {
    let len = lnga.max(lngb);
    let lhs = digit_slice(a, lnga).to_vec();
    let rhs = digit_slice(b, lngb).to_vec();
    *pborrow = mpn_sub_impl(&lhs, &rhs, digit_slice_mut(c, len));
}

pub unsafe fn mpn_mul(
    a: *const MpnDigit,
    lnga: usize,
    b: *const MpnDigit,
    lngb: usize,
    c: *mut MpnDigit,
) {
    let lhs = digit_slice(a, lnga).to_vec();
    let rhs = digit_slice(b, lngb).to_vec();
    mpn_mul_impl(&lhs, &rhs, digit_slice_mut(c, lnga + lngb));
}

pub unsafe fn mpn_div(
    numer: *const MpnDigit,
    lnum: usize,
    denom: *const MpnDigit,
    lden: usize,
    quot: *mut MpnDigit,
    rem: *mut MpnDigit,
) {
    let quot_len = if lnum >= lden { lnum - lden + 1 } else { 1 };
    mpn_div_impl(
        digit_slice(numer, lnum),
        digit_slice(denom, lden),
        digit_slice_mut(quot, quot_len),
        digit_slice_mut(rem, lden),
    );
}

pub unsafe fn mpn_to_string(
    a: *const MpnDigit,
    lng: usize,
    buf: *mut c_char,
    lbuf: usize,
) -> *mut c_char {
    if lbuf == 0 {
        return buf;
    }
    let digits = digit_slice(a, lng);
    let mut out = Vec::new();
    if lng == 1 {
        out.extend_from_slice(digits[0].to_string().as_bytes());
    } else {
        let mut temp = digits.to_vec();
        let ten = [10u32];
        while !temp.is_empty() && (temp.len() > 1 || temp[0] != 0) {
            let (shift, mut t_numer, t_denom) = div_normalize(&temp, &ten);
            div_1(&mut t_numer, t_denom[0], &mut temp);
            let mut rem = [0u32];
            div_unnormalize(&t_numer, t_denom.len(), shift, &mut rem);
            out.push(b'0' + rem[0] as u8);
            while !temp.is_empty() && *temp.last().unwrap() == 0 {
                temp.pop();
            }
        }
        out.reverse();
    }
    let copy_len = out.len().min(lbuf - 1);
    ptr::copy_nonoverlapping(out.as_ptr(), buf.cast::<u8>(), copy_len);
    *buf.add(copy_len) = 0;
    buf
}
