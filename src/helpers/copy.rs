use std::hash::{Hash, Hasher};
use std::mem::ManuallyDrop;
use std::ops::{Deref, DerefMut};

// Custom AES-based Hasher implementation
#[derive(Default)]
struct AesHasher {
    buffer: Vec<u8>,
}

impl Hasher for AesHasher {
    fn write(&mut self, bytes: &[u8]) {
        self.buffer.extend_from_slice(bytes);
    }

    fn finish(&self) -> u64 {
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        return hash_aarch64_fast(&self.buffer);

        #[cfg(all(target_arch = "x86_64", target_feature = "aes"))]
        return hash_x86_fast(&self.buffer);

        // Fallback for other platforms
        #[cfg(not(any(
            all(target_arch = "aarch64", target_feature = "aes"),
            all(target_arch = "x86_64", target_feature = "aes")
        )))]
        {
            use std::collections::hash_map::DefaultHasher;
            let mut s = DefaultHasher::new();
            s.write(&self.buffer);
            s.finish()
        }
    }
}

// Provided hash functions
#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
#[inline(always)]
pub fn hash_aarch64_fast(input: &[u8]) -> u64 {
    use std::arch::aarch64::*;

    unsafe {
        // Define your initial key as a [u8; 16] array
        let initial_key: [u8; 16] = [
            0xA1, 0x12, 0x02, 0xC9, 0xB4, 0x68, 0xBE, 0xA1,
            0xD7, 0x51, 0x57, 0xA0, 0x14, 0x52, 0x49, 0x5B,
        ];

        // Load the initial key into a SIMD vector using vld1q_u8
        let mut hash = vld1q_u8(initial_key.as_ptr());

        let chunks = input.chunks_exact(16);
        let remainder = chunks.remainder();

        // Process 128-bit chunks
        for chunk in chunks {
            let block = vld1q_u8(chunk.as_ptr());
            // Standard AES round: SubBytes + ShiftRows + MixColumns
            hash = vaeseq_u8(hash, block);
        }

        // Process remainder
        let mut tail = [0u8; 16];
        tail[..remainder.len()].copy_from_slice(remainder);
        let tail_block = vld1q_u8(tail.as_ptr());
        hash = vaeseq_u8(hash, tail_block);

        // "Finalization" round
        let finalization_key: [u8; 16] = [
            0x8E, 0x51, 0xEF, 0x21, 0xFA, 0xBB, 0x45, 0x22,
            0xE4, 0x3D, 0x7A, 0x06, 0x56, 0x95, 0x4B, 0x6C,
        ];
        let finalization_key_vec = vld1q_u8(finalization_key.as_ptr());
        hash = vaeseq_u8(hash, finalization_key_vec);

        // Convert to 128 bits
        let result: [u8; 16] = core::mem::transmute(hash);
        let high = u64::from_le_bytes(result[0..8].try_into().unwrap());
        let low = u64::from_le_bytes(result[8..16].try_into().unwrap());
        high ^ low
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "aes"))]
#[inline(always)]
pub fn hash_x86_fast(input: &[u8]) -> u64 {
    use core::arch::x86_64::{
        __m128i, _mm_aesenc_si128, _mm_extract_epi64, _mm_loadu_si128, _mm_set_epi64x,
    };

    unsafe {
        let mut hash = _mm_set_epi64x(0xA11202C9B468BEA1, 0xD75157A01452495B);

        let chunks = input.chunks_exact(16);
        let remainder = chunks.remainder();

        for chunk in chunks {
            let block: __m128i = _mm_loadu_si128(chunk.as_ptr() as *const __m128i);
            hash = _mm_aesenc_si128(hash, block);
        }

        let mut tail = [0u8; 16];
        tail[..remainder.len()].copy_from_slice(remainder);
        let tail_block = _mm_loadu_si128(tail.as_ptr() as *const __m128i);
        hash = _mm_aesenc_si128(hash, tail_block);

        let final_key = _mm_set_epi64x(0x8E51EF21FABB4522, 0xE43D7A0656954B6C);
        hash = _mm_aesenclast_si128(hash, final_key);

        let high = _mm_extract_epi64(hash, 0) as u64;
        let low = _mm_extract_epi64(hash, 1) as u64;
        high ^ low
    }
}

// A basic fixed-capacity HashMap using linear probing for collision resolution.
// The entire structure implements Copy, assuming K and V are Copy.
// Capacity is fixed at compile time via the const generic N.
#[derive(Copy, Clone)]
pub struct CopyHashMap<K: Copy + Eq + Hash, V: Copy, const N: usize> {
    buckets: [Option<(K, V)>; N],
}

impl<K: Copy + Eq + Hash, V: Copy, const N: usize> CopyHashMap<K, V, N> {
    /// Creates a new empty HashMap with fixed capacity N.
    pub fn new() -> Self {
        Self {
            buckets: [None; N],
        }
    }

    /// Computes the hash index for the given key using custom AES hasher.
    fn hash(&self, key: &K) -> usize {
        let mut hasher = AesHasher::default();
        key.hash(&mut hasher);
        (hasher.finish() as usize) % N
    }

    /// Inserts a key-value pair into the map.
    /// If the key already exists, updates the value.
    /// Panics if the map is full.
    pub fn insert(&mut self, key: K, value: V) {
        let h = self.hash(&key);

        // Linear probing to find the slot.
        for i in 0..N {
            let idx = (h + i) % N;
            match self.buckets[idx] {
                Some((ref k, _)) if *k == key => {
                    self.buckets[idx] = Some((key, value));
                    return;
                }
                None => {
                    self.buckets[idx] = Some((key, value));
                    return;
                }
                _ => {}
            }
        }
        panic!("HashMap is full");
    }

    /// Gets the value associated with the given key, if present.
    pub fn get(&self, key: &K) -> Option<V> {
        let h = self.hash(key);

        // Linear probing to find the key.
        for i in 0..N {
            let idx = (h + i) % N;
            match self.buckets[idx] {
                Some((ref k, ref v)) if *k == *key => return Some(*v),
                None => return None,
                _ => {}
            }
        }
        None
    }

    /// Removes the key-value pair for the given key, if present.
    /// Returns the removed value, or None if not found.
    /// Note: This implementation uses tombstoning (sets to None) for simplicity,
    /// but in a real hash map, you'd want to handle rehashing or better deletion.
    pub fn remove(&mut self, key: &K) -> Option<V> {
        let h = self.hash(key);

        for i in 0..N {
            let idx = (h + i) % N;
            match self.buckets[idx] {
                Some((ref k, ref v)) if *k == *key => {
                    let value = *v;
                    self.buckets[idx] = None;
                    return Some(value);
                }
                None => return None,
                _ => {}
            }
        }
        None
    }
}

// A basic fixed-capacity HashSet using linear probing for collision resolution.
// The entire structure implements Copy, assuming K is Copy.
// Capacity is fixed at compile time via the const generic N.
#[derive(Copy, Clone)]
pub struct CopyHashSet<K: Copy + Eq + Hash, const N: usize> {
    buckets: [Option<K>; N],
}

impl<K: Copy + Eq + Hash, const N: usize> CopyHashSet<K, N> {
    /// Creates a new empty HashSet with fixed capacity N.
    pub fn new() -> Self {
        Self {
            buckets: [None; N],
        }
    }

    /// Computes the hash index for the given key using custom AES hasher.
    fn hash(&self, key: &K) -> usize {
        let mut hasher = AesHasher::default();
        key.hash(&mut hasher);
        (hasher.finish() as usize) % N
    }

    /// Inserts a key into the set.
    /// Returns true if the key was not already present.
    /// Panics if the set is full.
    pub fn insert(&mut self, key: K) -> bool {
        let h = self.hash(&key);

        // Linear probing to find the slot.
        for i in 0..N {
            let idx = (h + i) % N;
            match self.buckets[idx] {
                Some(ref k) if *k == key => {
                    return false; // Already present
                }
                None => {
                    self.buckets[idx] = Some(key);
                    return true;
                }
                _ => {}
            }
        }
        panic!("HashSet is full");
    }

    /// Checks if the set contains the given key.
    pub fn contains(&self, key: &K) -> bool {
        let h = self.hash(key);

        // Linear probing to find the key.
        for i in 0..N {
            let idx = (h + i) % N;
            match self.buckets[idx] {
                Some(ref k) if *k == *key => return true,
                None => return false,
                _ => {}
            }
        }
        false
    }

    /// Removes the key from the set, if present.
    /// Returns true if the key was present and removed.
    /// Note: This implementation uses tombstoning (sets to None) for simplicity,
    /// but in a real hash set, you'd want to handle rehashing or better deletion.
    pub fn remove(&mut self, key: &K) -> bool {
        let h = self.hash(key);

        for i in 0..N {
            let idx = (h + i) % N;
            match self.buckets[idx] {
                Some(ref k) if *k == *key => {
                    self.buckets[idx] = None;
                    return true;
                }
                None => return false,
                _ => {}
            }
        }
        false
    }
}

// Example usage (commented out for compilation in isolation):
/*
fn main() {
    // HashMap example
    let mut map: CopyHashMap<i32, i32, 16> = CopyHashMap::new();
    map.insert(1, 10);
    map.insert(2, 20);
    println!("Value for 1: {:?}", map.get(&1)); // Some(10)
    map.insert(1, 100);
    println!("Value for 1: {:?}", map.get(&1)); // Some(100)
    map.remove(&2);
    println!("Value for 2: {:?}", map.get(&2)); // None

    // Demonstrate Copy: copy the entire map
    let map_copy = map;
    println!("Copied value for 1: {:?}", map_copy.get(&1)); // Some(100)
    println!("Original value for 1: {:?}", map.get(&1)); // Still Some(100)

    // HashSet example
    let mut set: CopyHashSet<i32, 16> = CopyHashSet::new();
    set.insert(1);
    set.insert(2);
    println!("Contains 1: {:?}", set.contains(&1)); // true
    set.insert(1); // Already present, returns false
    set.remove(&2);
    println!("Contains 2: {:?}", set.contains(&2)); // false

    // Demonstrate Copy: copy the entire set
    let set_copy = set;
    println!("Copied contains 1: {:?}", set_copy.contains(&1)); // true
    println!("Original contains 1: {:?}", set.contains(&1)); // true
}
*/

use std::mem;

// A fixed-capacity vector that implements Copy, assuming T is Copy.
// Capacity is fixed at compile time via the const generic N.
// This is safe, unlike the unsafe ManuallyDrop<Vec> version.
// It uses an array of Option<T> to store elements, but only up to len are valid.
// Elements beyond len are None.
#[derive(Copy, Clone)]
pub struct CopyVec<T: Copy, const N: usize> {
    data: [Option<T>; N],
    len: usize,
}

impl<T: Copy, const N: usize> CopyVec<T, N> {
    /// Creates a new empty CopyVec with fixed capacity N.
    pub fn new() -> Self {
        Self {
            data: [None; N],
            len: 0,
        }
    }

    /// Returns the number of elements in the vector.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if the vector is empty.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Pushes a value to the end of the vector.
    /// Panics if the vector is at capacity.
    pub fn push(&mut self, value: T) {
        if self.len >= N {
            panic!("CopyVec is full");
        }
        self.data[self.len] = Some(value);
        self.len += 1;
    }

    /// Pops the last value from the vector, if any.
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }
        self.len -= 1;
        let value = self.data[self.len];
        self.data[self.len] = None; // Optional, but clears the slot
        value
    }

    /// Gets a reference to the element at the given index, if in bounds.
    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len {
            None
        } else {
            self.data[index].as_ref()
        }
    }

    /// Gets a mutable reference to the element at the given index, if in bounds.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index >= self.len {
            None
        } else {
            self.data[index].as_mut()
        }
    }

    /// Sets the value at the given index, if in bounds.
    /// Returns the old value, if any.
    pub fn set(&mut self, index: usize, value: T) -> Option<T> {
        if index >= self.len {
            return None;
        }
        mem::replace(&mut self.data[index], Some(value))
    }

    /// Clears the vector, setting len to 0.
    /// Does not change the capacity.
    pub fn clear(&mut self) {
        for i in 0..self.len {
            self.data[i] = None;
        }
        self.len = 0;
    }
}

// Example usage (commented out for compilation in isolation):
/*
fn main() {
    let mut vec: CopyVec<i32, 16> = CopyVec::new();
    vec.push(1);
    vec.push(2);
    println!("Len: {}", vec.len()); // 2
    println!("Get 0: {:?}", vec.get(0)); // Some(&1)
    vec.set(0, 10);
    println!("Get 0: {:?}", vec.get(0)); // Some(&10)
    vec.pop();
    println!("Len: {}", vec.len()); // 1

    // Demonstrate Copy: copy the entire vec
    let vec_copy = vec;
    println!("Copied len: {}", vec_copy.len()); // 1
    println!("Original len: {}", vec.len()); // 1
}
*/

// A Copy-able fixed-capacity string, stored inline in an array.
#[derive(Copy, Clone, Debug)]
pub struct CopyString<const N: usize> {
    data: [u8; N],
    len: usize,
}

impl<const N: usize> CopyString<N> {
    /// Creates a new CopyString from a &str, if it fits within capacity.
    pub fn new(s: &str) -> Option<Self> {
        if s.len() > N {
            return None;
        }
        let mut data = [0u8; N];
        data[..s.len()].copy_from_slice(s.as_bytes());
        Some(Self { data, len: s.len() })
    }

    /// Returns the string as a &str slice.
    pub fn as_str(&self) -> &str {
        // Safe assuming input was valid UTF-8.
        std::str::from_utf8(&self.data[..self.len]).unwrap()
    }

    /// Updates the string if the new value fits within capacity.
    pub fn save(&mut self, s: &str) -> Result<(), ()> {
        if s.len() > N {
            return Err(());
        }
        self.data[..s.len()].copy_from_slice(s.as_bytes());
        self.len = s.len();
        // Zero out the rest for safety (optional, but good hygiene).
        self.data[s.len()..].fill(0);
        Ok(())
    }
}

/*
fn main() {
    let s1 = CopyString::<16>::new("hello").unwrap();
    let s2 = s1;  // Bitwise copy, no clone needed!
    println!("{}", s2.as_str());  // Outputs: hello
}
*/