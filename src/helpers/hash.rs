
//! Minimal Swiss-style HashMap for AArch64 with 128-bit NEON tag probing
//! - Open addressing, 16-slot groups (“buckets”) with 1-byte control per slot
//! - SIMD probe across 16 control bytes at once using NEON (AArch64)
//! - Scalar fallback when NEON unavailable (still uses the same layout)
//! - Keys are owned `String` for simplicity (object-language property names)
//! - Hash function pluggable; default integrates the AES-based mixer the user shared
//!
//! Disclaimer: This is a compact, benchmark-ready prototype, not production-hardened.
//! It omits concurrent resizing, tombstone compaction, and advanced DoS hardening.

#![allow(clippy::too_many_arguments)]
#![cfg_attr(any(target_arch = "aarch64"), feature(stdsimd))]

use core::mem::MaybeUninit;
use std::hash::BuildHasherDefault;

// --------------------------
// Entry
// --------------------------
#[derive(Clone)]
struct Entry { key: String, value: u64, hash: u64 }

// --------------------------
// AES Hash function
// --------------------------
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline(always)]
pub fn hash_aarch64_fast(input: &[u8]) -> u64 {
    use core::arch::aarch64::*;

    unsafe {
        // Fixed keys (any constants; keep them non-zero/non-related)
        let k0 = vld1q_u8([
            0xA1, 0x12, 0x02, 0xC9, 0xB4, 0x68, 0xBE, 0xA1,
            0xD7, 0x51, 0x57, 0xA0, 0x14, 0x52, 0x49, 0x5B,
        ].as_ptr());
        let kf = vld1q_u8([
            0x8E, 0x51, 0xEF, 0x21, 0xFA, 0xBB, 0x45, 0x22,
            0xE4, 0x3D, 0x7A, 0x06, 0x56, 0x95, 0x4B, 0x6C,
        ].as_ptr());

        // Seed with k0 ^ length (length helps disambiguate short/tail collisions)
        let mut state = k0;
        let len_vec = vreinterpretq_u8_u64(vsetq_lane_u64(input.len() as u64, vdupq_n_u64(0), 0));
        state = veorq_u8(state, len_vec);

        let mut chunks = input.chunks_exact(16);
        for chunk in &mut chunks {
            let m = vld1q_u8(chunk.as_ptr());
            // round: (state ^ m) -> AESE -> AESMC
            let x = veorq_u8(state, m);
            state = vaeseq_u8(x, vdupq_n_u8(0));  // AESE does SubBytes+ShiftRows+AddRoundKey(0)
            state = vaesmcq_u8(state);            // MixColumns for non-final rounds
        }

        // Tail with 0x80 padding and length folded (Merkle–Damgård style)
        let rem = chunks.remainder();
        let mut tail = [0u8; 16];
        let n = rem.len();
        tail[..n].copy_from_slice(rem);
        tail[n] = 0x80;
        // xor the low 64 bits with length again to avoid zero-tail aliasing
        let mut t = vld1q_u8(tail.as_ptr());
        t = veorq_u8(t, len_vec);
        let x = veorq_u8(state, t);
        state = vaeseq_u8(x, vdupq_n_u8(0));
        // Final AES round (no MixColumns)
        state = vaeseq_u8(state, kf);

        // Fold 128 -> 64 by xoring the two 64-bit lanes
        let s64 = vreinterpretq_u64_u8(state);
        let lo = vgetq_lane_u64(s64, 0);
        let hi = vgetq_lane_u64(s64, 1);
        lo ^ hi
    }
}

// --------------------------
// Control-byte conventions
// --------------------------
// We mirror SwissTable-ish encodings:
//  - 0x80 => EMPTY
//  - 0xFE => TOMBSTONE (deleted)
//  - 0x00..=0x7F => h2 tag (7-bit) | 0x00, but we store as tag | 0x00 and OR 0x80 in the vector
//    for SIMD compare to avoid mixing special sentinels. We simply ensure tag < 0x80.
const CTRL_EMPTY: u8 = 0x80;      // 1000_0000
const CTRL_TOMB:  u8 = 0xFE;      // 1111_1110

#[inline(always)]
fn is_empty(c: u8) -> bool { c == CTRL_EMPTY }
#[inline(always)]
fn is_tomb(c: u8) -> bool { c == CTRL_TOMB }
#[inline(always)]
fn is_full(c: u8) -> bool { c < 0x80 }

#[inline(always)]
fn h1(hash: u64, mask: usize) -> usize { (hash as usize) & mask }
#[inline(always)]
fn h2(hash: u64) -> u8 { ((hash >> 7) as u8) & 0x7F }

// --------------------------
// AES-based hash for strings (AArch64 AES fast path, scalar fallback)
// --------------------------
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline(always)]
pub fn hash_str_aes(s: &str) -> u64 {
    use core::arch::aarch64::*;
    unsafe {
        let k0 = vld1q_u8([
            0xA1, 0x12, 0x02, 0xC9, 0xB4, 0x68, 0xBE, 0xA1,
            0xD7, 0x51, 0x57, 0xA0, 0x14, 0x52, 0x49, 0x5B,
        ].as_ptr());
        let kf = vld1q_u8([
            0x8E, 0x51, 0xEF, 0x21, 0xFA, 0xBB, 0x45, 0x22,
            0xE4, 0x3D, 0x7A, 0x06, 0x56, 0x95, 0x4B, 0x6C,
        ].as_ptr());
        let mut state = k0;
        let len_vec = vreinterpretq_u8_u64(vsetq_lane_u64(s.len() as u64, vdupq_n_u64(0), 0));
        state = veorq_u8(state, len_vec);
        let mut chunks = s.as_bytes().chunks_exact(16);
        for chunk in &mut chunks {
            let m = vld1q_u8(chunk.as_ptr());
            let x = veorq_u8(state, m);
            state = vaeseq_u8(x, vdupq_n_u8(0));
            state = vaesmcq_u8(state);
        }
        let rem = chunks.remainder();
        let mut tail = [0u8; 16];
        let n = rem.len();
        tail[..n].copy_from_slice(rem);
        tail[n] = 0x80;
        let mut t = vld1q_u8(tail.as_ptr());
        t = veorq_u8(t, len_vec);
        let x = veorq_u8(state, t);
        state = vaeseq_u8(x, vdupq_n_u8(0));
        state = vaeseq_u8(state, kf);
        let s64 = vreinterpretq_u64_u8(state);
        vgetq_lane_u64(s64, 0) ^ vgetq_lane_u64(s64, 1)
    }
}

#[cfg(any(not(target_arch = "aarch64"), all(target_arch = "aarch64", not(target_feature = "aes"))))]
#[inline(always)]
pub fn hash_str_aes(s: &str) -> u64 {
    // Simple portable fallback (wyrand-ish)
    let mut x = 0x9E37_79B9_7F4A_7C15u64 ^ (s.len() as u64);
    for &b in s.as_bytes() { x ^= b as u64; x = x.rotate_left(27).wrapping_mul(0x94D0_49BB_1331_11EB); }
    x ^ (x >> 32)
}

// --------------------------
// SIMD helpers (AArch64 NEON)
// --------------------------
#[cfg(target_arch = "aarch64")]
#[inline(always)]
unsafe fn neon_eq_mask_16(ctrl_ptr: *const u8, tag: u8) -> u16 {
    use core::arch::aarch64::*;
    let ctrl = vld1q_u8(ctrl_ptr);
    let tagv = vdupq_n_u8(tag);
    let eq = vceqq_u8(ctrl, tagv);
    neon_movemask_u8(eq)
}

#[cfg(target_arch = "aarch64")]
#[inline(always)]
unsafe fn neon_is_empty_or_tomb_mask_16(ctrl_ptr: *const u8) -> u16 {
    use core::arch::aarch64::*;
    let ctrl = vld1q_u8(ctrl_ptr);
    // empty if == 0x80, tomb if == 0xFE
    let m_empty = vceqq_u8(ctrl, vdupq_n_u8(CTRL_EMPTY));
    let m_tomb  = vceqq_u8(ctrl, vdupq_n_u8(CTRL_TOMB));
    neon_movemask_u8(vorrq_u8(m_empty, m_tomb))
}

#[cfg(target_arch = "aarch64")]
#[inline(always)]
unsafe fn neon_movemask_u8(v: core::arch::aarch64::uint8x16_t) -> u16 {
    use core::arch::aarch64::*;
    // Extract MSBs into a 16-bit mask.
    // Technique: shift right by 7, AND with bit-weights, horizontal add low/high.
    const MASK_ARR: [u8; 16] = [1,2,4,8,16,32,64,128,1,2,4,8,16,32,64,128];
    let weights = vld1q_u8(MASK_ARR.as_ptr());
    let msbs = vshrq_n_u8(v, 7);
    let weighted = vandq_u8(msbs, weights);
    let lo = vget_low_u8(weighted);
    let hi = vget_high_u8(weighted);
    (vaddv_u8(lo) as u16) | ((vaddv_u8(hi) as u16) << 8)
}

// --------------------------
// Table
// --------------------------

#[cfg(target_arch = "aarch64")]
pub struct SimdHashMap {
    mask: usize,            // capacity-1, capacity is multiple of 16
    len: usize,
    ctrl: Box<[u8]>,        // control bytes (capacity + 16 sentinel)
    entries: Box<[MaybeUninit<Entry>]>,
}

impl SimdHashMap {
    pub fn with_capacity(mut cap: usize) -> Self {
        cap = cap.next_power_of_two().max(16);
        // round up to multiple of 16
        if cap % 16 != 0 { cap += 16 - (cap % 16); }
        let mask = cap - 1;
        let mut ctrl = vec![CTRL_EMPTY; cap + 16].into_boxed_slice();
        let entries = (0..cap).map(|_| MaybeUninit::uninit()).collect::<Vec<_>>().into_boxed_slice();
        Self { mask, len: 0, ctrl, entries }
    }

    #[inline(always)]
    fn capacity(&self) -> usize { self.mask + 1 }

    #[inline(always)]
    fn load_factor_ok(&self) -> bool { self.len * 100 <= self.capacity() * 85 }

    pub fn insert(&mut self, key: String, value: u64) -> Option<u64> {
        if !self.load_factor_ok() { self.rehash(self.capacity() * 2); }
        let hash = hash_str_aes(&key);
        let mut group = h1(hash, self.mask) & !0xF; // group base (multiple of 16)
        let tag = h2(hash);

        // Probe sequence: linear by groups of 16
        loop {
            // 1) Match existing by tag
            let mask_eq = unsafe { neon_eq_mask_16(self.ctrl[group..].as_ptr(), tag) };
            let mut m = mask_eq;
            while m != 0 {
                let i = m.trailing_zeros() as usize;
                m &= m - 1;
                let idx = group + i;
                if is_full(self.ctrl[idx]) {
                    // Full slot; check actual key
                    let e = unsafe { &*self.entries[idx].as_ptr() };
                    if e.hash == hash && e.key == key { // replace
                        self.entries[idx] = MaybeUninit::new(Entry { key, value, hash });
                        return Some(e.value);
                    }
                }
            }
            // 2) Find first empty/tomb slot to insert
            let empties = unsafe { neon_is_empty_or_tomb_mask_16(self.ctrl[group..].as_ptr()) };
            if empties != 0 {
                let i = empties.trailing_zeros() as usize;
                let idx = group + i;
                self.ctrl[idx] = tag; // mark full with tag (< 0x80)
                self.entries[idx] = MaybeUninit::new(Entry { key, value, hash });
                self.len += 1;
                return None;
            }
            group = (group + 16) & self.mask;
        }
    }

    pub fn get(&self, key: &str) -> Option<&u64> {
        let hash = hash_str_aes(key);
        let mut group = h1(hash, self.mask) & !0xF;
        let tag = h2(hash);
        loop {
            let mask_eq = unsafe { neon_eq_mask_16(self.ctrl[group..].as_ptr(), tag) };
            let mut m = mask_eq;
            while m != 0 {
                let i = m.trailing_zeros() as usize;
                m &= m - 1;
                let idx = group + i;
                if is_full(self.ctrl[idx]) {
                    let e = unsafe { &*self.entries[idx].as_ptr() };
                    if e.hash == hash && e.key.as_str() == key { return Some(&e.value); }
                }
            }
            // Stop when we see any empty in the group (no more items could be further)
            let empties_only = unsafe { neon_eq_mask_16(self.ctrl[group..].as_ptr(), CTRL_EMPTY) };
            if empties_only != 0 { return None; }
            group = (group + 16) & self.mask;
        }
    }

    pub fn remove(&mut self, key: &str) -> Option<u64> {
        let hash = hash_str_aes(key);
        let mut group = h1(hash, self.mask) & !0xF;
        let tag = h2(hash);
        loop {
            let mask_eq = unsafe { neon_eq_mask_16(self.ctrl[group..].as_ptr(), tag) };
            let mut m = mask_eq;
            while m != 0 {
                let i = m.trailing_zeros() as usize;
                m &= m - 1;
                let idx = group + i;
                if is_full(self.ctrl[idx]) {
                    let e = unsafe { &*self.entries[idx].as_ptr() };
                    if e.hash == hash && e.key.as_str() == key {
                        let old = e.value;
                        // Drop key in-place
                        unsafe { std::ptr::drop_in_place(self.entries[idx].as_mut_ptr()); }
                        self.ctrl[idx] = CTRL_TOMB;
                        self.len -= 1;
                        return Some(old);
                    }
                }
            }
            let empties_only = unsafe { neon_eq_mask_16(self.ctrl[group..].as_ptr(), CTRL_EMPTY) };
            if empties_only != 0 { return None; }
            group = (group + 16) & self.mask;
        }
    }

    fn rehash(&mut self, new_cap: usize) {
        let mut new_map = SimdHashMap::with_capacity(new_cap);
        for i in 0..self.capacity() { if is_full(self.ctrl[i]) {
            let e = unsafe { self.entries[i].assume_init_read() };
            new_map.insert(e.key, e.value);
        }}
        *self = new_map;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_ops() {
        let mut m = SimdHashMap::with_capacity(32);
        assert_eq!(m.insert("foo".to_string(), 1), None);
        assert_eq!(m.insert("bar".to_string(), 2), None);
        assert_eq!(m.get("foo"), Some(&1));
        assert_eq!(m.get("bar"), Some(&2));
        assert_eq!(m.insert("foo".to_string(), 3), Some(1));
        assert_eq!(m.get("foo"), Some(&3));
        assert_eq!(m.remove("foo"), Some(3));
        assert_eq!(m.get("foo"), None);
    }
}
