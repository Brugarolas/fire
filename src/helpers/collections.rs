// src/helpers.rs
#![allow(clippy::needless_range_loop)]
use std::cmp::Eq;
use std::hash::{BuildHasher, Hash, Hasher};
use std::iter::FromIterator;
use std::ops::{Deref, DerefMut};

/// ------------------------
/// TLS PRNG (no syscalls, no heap)
/// ------------------------
mod tls_prng {
    use std::cell::Cell;

    #[inline(always)]
    fn splitmix64_stateless(mut z: u64) -> u64 {
        z ^= z >> 30;
        z = z.wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z ^= z >> 27;
        z = z.wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    #[inline(always)]
    fn rdcycle_best_effort() -> u64 {
        let mut v: u64 = 0;
        #[cfg(target_arch = "x86_64")]
        unsafe {
            v ^= core::arch::x86_64::_rdtsc();
        }
        #[cfg(all(target_arch = "x86", not(target_arch = "x86_64")))]
        unsafe {
            v ^= core::arch::x86::_rdtsc() as u64;
        }
        #[cfg(target_arch = "aarch64")]
        unsafe {
            let cntvct: u64;
            core::arch::asm!("mrs {0}, cntvct_el0", out(reg) cntvct);
            v ^= cntvct;
        }
        v
    }

    #[inline(always)]
    fn addr_noise() -> u64 {
        let stack_addr = {
            let local = 0u8;
            (&local as *const u8 as usize as u64)
        };
        let code_addr = fast_two_u64 as usize as u64;
        stack_addr.rotate_left(17) ^ code_addr.rotate_left(31)
    }

    thread_local! {
        static TL_SEED: Cell<u64> = Cell::new(0);
        static TL_BOOTCTR: Cell<u64> = Cell::new(0);
    }

    #[inline(always)]
    fn initial_seed() -> u64 {
        TL_BOOTCTR.with(|c| {
            let ctr = {
                let v = c.get().wrapping_add(0x9E37_79B9_7F4A_7C15);
                c.set(v);
                v
            };
            let raw = rdcycle_best_effort() ^ addr_noise() ^ ctr;
            splitmix64_stateless(raw)
        })
    }

    #[inline(always)]
    fn wyrand_next(seed_cell: &Cell<u64>) -> u64 {
        let mut s = seed_cell.get();
        if s == 0 {
            s = initial_seed();
        }
        s = s.wrapping_add(0xA076_1D64_78BD_642F);
        let z = s;
        let t = (z as u128)
            .wrapping_mul((z ^ 0xE703_7ED1_A0B4_28DBu64) as u128);
        let out = ((t >> 64) as u64) ^ (t as u64);
        seed_cell.set(s);
        out
    }

    /// Return two u64 from the per-thread generator.
    #[inline(always)]
    pub fn fast_two_u64() -> (u64, u64) {
        TL_SEED.with(|seed| {
            let a = wyrand_next(seed);
            let b = wyrand_next(seed);
            (a, b)
        })
    }
}
use tls_prng::fast_two_u64;

/// ------------------------
/// AES-keyed Hasher backends
/// ------------------------
#[cfg(all(target_arch = "x86_64", target_feature = "aes"))]
mod hasher_impl {
    use super::*;
    use core::arch::x86_64::{
        __m128i, _mm_aesenc_si128, _mm_aesenclast_si128, _mm_loadu_si128, _mm_set_epi64x,
        _mm_storeu_si128, _mm_xor_si128,
    };

    pub struct AesHasher {
        hash: __m128i,
        buffer: [u8; 16],
        len: usize,
    }

    impl AesHasher {
        #[inline(always)]
        pub fn with_keys(k0: u64, k1: u64) -> Self {
            // lanes: hi=k0, lo=k1 (consistent across targets)
            unsafe {
                Self {
                    hash: _mm_set_epi64x(k0 as i64, k1 as i64),
                    buffer: [0; 16],
                    len: 0,
                }
            }
        }

        #[inline(always)]
        unsafe fn round(&mut self, block_ptr: *const u8) {
            let block = _mm_loadu_si128(block_ptr as *const __m128i);
            self.hash = _mm_aesenc_si128(self.hash, block);
        }

        #[inline(always)]
        fn mix_len(&mut self) {
            unsafe {
                // XOR message length and its bitwise NOT into lanes
                let len = self.len as u64;
                let len_vec =
                    _mm_set_epi64x(!(len) as i64, len as i64);
                self.hash = _mm_xor_si128(self.hash, len_vec);
            }
        }

        #[inline(always)]
        fn fold128(x: __m128i) -> u64 {
            unsafe {
                let mut tmp = core::mem::MaybeUninit::<[u8; 16]>::uninit();
                _mm_storeu_si128(tmp.as_mut_ptr() as *mut __m128i, x);
                let bytes = tmp.assume_init();
                let a = u64::from_ne_bytes(bytes[0..8].try_into().unwrap());
                let b = u64::from_ne_bytes(bytes[8..16].try_into().unwrap());
                a ^ b
            }
        }
    }

    impl Hasher for AesHasher {
        #[inline(always)]
        fn write(&mut self, mut bytes: &[u8]) {
            let buf_pos = self.len & 15;
            self.len = self.len.wrapping_add(bytes.len());

            if buf_pos != 0 {
                let to_fill = (16 - buf_pos).min(bytes.len());
                self.buffer[buf_pos..buf_pos + to_fill].copy_from_slice(&bytes[..to_fill]);
                bytes = &bytes[to_fill..];
                if buf_pos + to_fill == 16 {
                    unsafe { self.round(self.buffer.as_ptr()); }
                }
            }

            let mut chunks = bytes.chunks_exact(16);
            for chunk in &mut chunks {
                unsafe { self.round(chunk.as_ptr()); }
            }
            let rem = chunks.remainder();
            if !rem.is_empty() {
                self.buffer[..rem.len()].copy_from_slice(rem);
            }
        }

        #[inline(always)]
        fn write_u64(&mut self, i: u64) { self.write(&i.to_ne_bytes()); }
        #[inline(always)]
        fn write_u32(&mut self, i: u32) { self.write(&i.to_ne_bytes()); }
        #[inline(always)]
        fn write_u8(&mut self, i: u8) { self.write(&[i]); }

        #[inline(always)]
        fn finish(&self) -> u64 {
            unsafe {
                let mut cur = self.hash;
                let rem = self.len & 15;
                if rem != 0 {
                    let mut tail = [0u8; 16];
                    tail[..rem].copy_from_slice(&self.buffer[..rem]);
                    let block = _mm_loadu_si128(tail.as_ptr() as *const __m128i);
                    cur = _mm_aesenc_si128(cur, block);
                }

                // length mixing
                let len = self.len as u64;
                let len_vec = _mm_set_epi64x(!(len) as i64, len as i64);
                cur = _mm_xor_si128(cur, len_vec);

                // final round
                let final_key = _mm_set_epi64x(0x8E51EF21FABB4522u64 as i64, 0xE43D7A0656954B6Cu64 as i64);
                cur = _mm_aesenclast_si128(cur, final_key);

                Self::fold128(cur)
            }
        }
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
mod hasher_impl {
    use super::*;
    use core::arch::aarch64::*;

    #[inline(always)]
    unsafe fn aes_round_arm(state: uint8x16_t, rk: uint8x16_t) -> uint8x16_t {
        // Equivalent to x86 AESENC (SubBytes+ShiftRows, AddRoundKey, MixColumns)
        vaesmcq_u8(vaeseq_u8(state, rk))
    }
    #[inline(always)]
    unsafe fn aes_last_round_arm(state: uint8x16_t, rk: uint8x16_t) -> uint8x16_t {
        // Final round without MixColumns
        vaeseq_u8(state, rk)
    }

    pub struct AesHasher {
        hash: uint8x16_t,
        buffer: [u8; 16],
        len: usize,
    }

    impl AesHasher {
        #[inline(always)]
        pub fn with_keys(k0: u64, k1: u64) -> Self {
            // lanes: [lo bytes of k1][lo bytes of k0]
            let mut key = [0u8; 16];
            key[..8].copy_from_slice(&k1.to_ne_bytes());
            key[8..].copy_from_slice(&k0.to_ne_bytes());
            unsafe {
                Self {
                    hash: vld1q_u8(key.as_ptr()),
                    buffer: [0; 16],
                    len: 0,
                }
            }
        }
    }

    impl Hasher for AesHasher {
        #[inline(always)]
        fn write(&mut self, mut bytes: &[u8]) {
            let buf_pos = self.len & 15;
            self.len = self.len.wrapping_add(bytes.len());

            if buf_pos != 0 {
                let to_fill = (16 - buf_pos).min(bytes.len());
                self.buffer[buf_pos..buf_pos + to_fill].copy_from_slice(&bytes[..to_fill]);
                bytes = &bytes[to_fill..];
                if buf_pos + to_fill == 16 {
                    unsafe {
                        let block = vld1q_u8(self.buffer.as_ptr());
                        self.hash = aes_round_arm(self.hash, block);
                    }
                }
            }

            let mut chunks = bytes.chunks_exact(16);
            for chunk in &mut chunks {
                unsafe {
                    let block = vld1q_u8(chunk.as_ptr());
                    self.hash = aes_round_arm(self.hash, block);
                }
            }
            let rem = chunks.remainder();
            if !rem.is_empty() {
                self.buffer[..rem.len()].copy_from_slice(rem);
            }
        }

        #[inline(always)]
        fn write_u64(&mut self, i: u64) { self.write(&i.to_ne_bytes()); }
        #[inline(always)]
        fn write_u32(&mut self, i: u32) { self.write(&i.to_ne_bytes()); }
        #[inline(always)]
        fn write_u8(&mut self, i: u8) { self.write(&[i]); }

        #[inline(always)]
        fn finish(&self) -> u64 {
            unsafe {
                let mut cur = self.hash;
                let rem = self.len & 15;
                if rem != 0 {
                    let mut tail = [0u8; 16];
                    tail[..rem].copy_from_slice(&self.buffer[..rem]);
                    let block = vld1q_u8(tail.as_ptr());
                    cur = aes_round_arm(cur, block);
                }

                // length mixing
                let mut len_block = [0u8; 16];
                len_block[..8].copy_from_slice(&(self.len as u64).to_ne_bytes());
                len_block[8..].copy_from_slice(&(!(self.len as u64)).to_ne_bytes());
                let len_vec = vld1q_u8(len_block.as_ptr());
                cur = veorq_u8(cur, len_vec);

                // final round
                let final_key: [u8; 16] = [
                    0x8E, 0x51, 0xEF, 0x21, 0xFA, 0xBB, 0x45, 0x22,
                    0xE4, 0x3D, 0x7A, 0x06, 0x56, 0x95, 0x4B, 0x6C,
                ];
                let fk = vld1q_u8(final_key.as_ptr());
                cur = aes_last_round_arm(cur, fk);

                let mut out = [0u8; 16];
                vst1q_u8(out.as_mut_ptr(), cur);
                let a = u64::from_ne_bytes(out[0..8].try_into().unwrap());
                let b = u64::from_ne_bytes(out[8..16].try_into().unwrap());
                a ^ b
            }
        }
    }
}

#[cfg(not(any(
    all(target_arch = "x86_64", target_feature = "aes"),
    all(target_arch = "aarch64", target_feature = "aes")
)))]
mod hasher_impl {
    use super::*;
    use ahash::AHasher;

    #[derive(Default)]
    pub struct AesHasher(pub AHasher);

    impl AesHasher {
        #[inline(always)]
        pub fn with_keys(k0: u64, k1: u64) -> Self {
            Self(AHasher::new_with_keys(k0, k1))
        }
    }

    impl Hasher for AesHasher {
        #[inline(always)]
        fn write(&mut self, bytes: &[u8]) { self.0.write(bytes) }
        #[inline(always)]
        fn write_u64(&mut self, i: u64) { self.0.write_u64(i) }
        #[inline(always)]
        fn write_u32(&mut self, i: u32) { self.0.write_u32(i) }
        #[inline(always)]
        fn write_u8(&mut self, i: u8) { self.0.write_u8(i) }
        #[inline(always)]
        fn finish(&self) -> u64 { self.0.finish() }
    }
}

use hasher_impl::AesHasher;

/// ------------------------
/// BuildHasher with per-map keys (no syscalls)
/// ------------------------
#[derive(Clone, Copy, Debug)]
pub struct AesBuildHasher {
    k0: u64,
    k1: u64,
}
impl AesBuildHasher {
    #[inline]
    pub fn new() -> Self {
        let (k0, k1) = fast_two_u64();
        Self { k0, k1 }
    }
    #[inline]
    pub fn from_seed(k0: u64, k1: u64) -> Self {
        Self { k0, k1 }
    }
}
impl Default for AesBuildHasher {
    #[inline]
    fn default() -> Self { Self::new() }
}
impl BuildHasher for AesBuildHasher {
    type Hasher = AesHasher;
    #[inline]
    fn build_hasher(&self) -> Self::Hasher { AesHasher::with_keys(self.k0, self.k1) }
}

/// ------------------------
/// Collections (hashbrown + papaya) wired to AesBuildHasher
/// ------------------------

// Concurrent map (papaya)
#[derive(Debug)]
pub struct ConcurrentHashMap<K: Eq + Hash, V>(pub papaya::HashMap<K, V, AesBuildHasher>);
impl<K: Eq + Hash, V> ConcurrentHashMap<K, V> {
    #[inline] pub fn new() -> Self { Self(papaya::HashMap::with_hasher(AesBuildHasher::new())) }
}
impl<K: Eq + Hash, V> Default for ConcurrentHashMap<K, V> {
    #[inline] fn default() -> Self { Self::new() }
}
impl<K: Eq + Hash, V> Deref for ConcurrentHashMap<K, V> {
    type Target = papaya::HashMap<K, V, AesBuildHasher>;
    #[inline] fn deref(&self) -> &Self::Target { &self.0 }
}
impl<K: Eq + Hash, V> DerefMut for ConcurrentHashMap<K, V> {
    #[inline] fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}

// hashbrown::HashMap
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HashMap<K: Eq + Hash, V>(pub hashbrown::HashMap<K, V, AesBuildHasher>);
impl<K: Eq + Hash, V> HashMap<K, V> {
    #[inline] pub fn new() -> Self { Self(hashbrown::HashMap::with_hasher(AesBuildHasher::new())) }
    #[inline] pub fn with_capacity(cap: usize) -> Self {
        Self(hashbrown::HashMap::with_capacity_and_hasher(cap, AesBuildHasher::new()))
    }

    #[inline]
    pub fn get_internals(&self) -> &hashbrown::HashMap<K, V, AesBuildHasher> {
        &self.0
    }
}
impl<K: Eq + Hash, V> Default for HashMap<K, V> { #[inline] fn default() -> Self { Self::new() } }
impl<K: Eq + Hash, V> Deref for HashMap<K, V> {
    type Target = hashbrown::HashMap<K, V, AesBuildHasher>;
    #[inline] fn deref(&self) -> &Self::Target { &self.0 }
}
impl<K: Eq + Hash, V> DerefMut for HashMap<K, V> {
    #[inline] fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}
impl<K: Eq + Hash, V> FromIterator<(K, V)> for HashMap<K, V> {
    #[inline]
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut m = hashbrown::HashMap::with_hasher(AesBuildHasher::new());
        m.extend(iter);
        Self(m)
    }
}

impl<K: Eq + Hash, V> IntoIterator for HashMap<K, V> {
    type Item = (K, V);
    type IntoIter = hashbrown::hash_map::IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

// hashbrown::HashSet
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HashSet<T: Eq + Hash>(pub hashbrown::HashSet<T, AesBuildHasher>);
impl<T: Eq + Hash> HashSet<T> {
    #[inline] pub fn new() -> Self { Self(hashbrown::HashSet::with_hasher(AesBuildHasher::new())) }
    #[inline] pub fn with_capacity(cap: usize) -> Self {
        Self(hashbrown::HashSet::with_capacity_and_hasher(cap, AesBuildHasher::new()))
    }

    #[inline]
    pub fn get_internals(&self) -> &hashbrown::HashSet<T, AesBuildHasher> {
        &self.0
    }
}
impl<T: Eq + Hash> Default for HashSet<T> { #[inline] fn default() -> Self { Self::new() } }
impl<T: Eq + Hash> Deref for HashSet<T> {
    type Target = hashbrown::HashSet<T, AesBuildHasher>;
    #[inline] fn deref(&self) -> &Self::Target { &self.0 }
}
impl<T: Eq + Hash> DerefMut for HashSet<T> {
    #[inline] fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}
impl<T: Eq + Hash> FromIterator<T> for HashSet<T> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut s = hashbrown::HashSet::with_hasher(AesBuildHasher::new());
        s.extend(iter);
        Self(s)
    }
}
