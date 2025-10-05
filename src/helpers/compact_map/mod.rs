// helpers/compact_map/mod.rs
#[macro_use]
mod macros;
mod inline;
mod raw;

use core::{
    hash::{BuildHasher, Hash},
    hint::unreachable_unchecked,
    iter::FusedIterator,
};
use std::{
    collections::hash_map::RandomState,
    fmt::{self, Debug},
};

use hashbrown::HashMap;
use crate::helpers::collections::AesBuildHasher;
use inline::Inline;

pub use hashbrown::Equivalent;

pub const INLINE_CAPACITY: usize = 64;

#[derive(Clone)]
pub enum CompactMap<K, V> {
    Heap(HashMap<K, V, AesBuildHasher>),
    Inline(Inline<K, V>),
}

impl<K, V> Debug for CompactMap<K, V>
where
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V: Default> Default for CompactMap<K, V> {
    /// Creates an empty `CompactMap<K, V>`.
    ///
    /// You can specify all types of CompactMap, including N and hasher.
    /// The created map is empty and doesn't allocate memory
    ///
    /// let map: CompactMap<u32, String> = CompactMap::default();
    /// ```
    #[inline]
    fn default() -> Self {
        Self::Inline(Inline::default())
    }
}

impl<K, V: Default> CompactMap<K, V> {
    /// Creates an empty `CompactMap`.
    #[inline]
    fn new() -> Self {
        Self::default()
    }

    /// Creates an empty `CompactMap` with the specified capacity.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        if capacity > 64 {
            Self::Heap(HashMap::with_capacity_and_hasher(
                capacity,
                AesBuildHasher::default(),
            ))
        } else {
            Self::Inline(Inline::default())
        }
    }
}

impl<K, V> CompactMap<K, V> {
    /// What branch it is now.
    #[inline]
    pub fn is_inline(&self) -> bool {
        matches!(self, Self::Inline(..))
    }

    /// Returns the number of elements the map can hold without reallocating.
    ///
    /// This number is a lower bound; the `CompactMap<K, V>` might be able to hold
    /// more, but is guaranteed to be able to hold at least this many.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_map::CompactMap;
    ///
    /// let map: CompactMap<i32, i32> = CompactMap::with_capacity(100);
    /// assert_eq!(map.len(), 0);
    /// assert!(map.capacity() >= 100);
    ///
    /// let map: CompactMap<i32, i32> = CompactMap::with_capacity(2);
    /// assert_eq!(map.len(), 0);
    /// assert!(map.capacity() >= 8);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        match self {
            CompactMap::Heap(inner) => inner.capacity(),
            CompactMap::Inline(_) => 64,
        }
    }
}

impl<K, V> CompactMap<K, V>
where
    K: Eq + Hash,
{
    #[inline]
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where
        Q: Hash + Equivalent<K>,
    {
        match self {
            CompactMap::Heap(inner) => inner.get(k),
            CompactMap::Inline(inner) => inner.get(k),
        }
    }

    /// Returns a mutable reference to the value corresponding to the key.
    #[inline]
    pub fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V>
    where
        Q: Hash + Equivalent<K>,
    {
        match self {
            CompactMap::Heap(inner) => inner.get_mut(k),
            CompactMap::Inline(inner) => inner.get_mut(k),
        }
    }

    /// Returns the key-value pair corresponding to the supplied key.
    #[inline]
    pub fn get_key_value<Q: ?Sized>(&self, k: &Q) -> Option<(&K, &V)>
    where
        Q: Hash + Equivalent<K>,
    {
        match self {
            CompactMap::Heap(inner) => inner.get_key_value(k),
            CompactMap::Inline(inner) => inner.get_key_value(k),
        }
    }

    #[inline]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        match self {
            CompactMap::Heap(inner) => inner.insert(key, value),
            CompactMap::Inline(inner) => {
                if raw::util::likely(!inner.is_full()) {
                    return inner.insert(key, value);
                }
                let heap = HashMap::with_capacity_and_hasher(INLINE_CAPACITY * 2, AesBuildHasher::default());

                let heap = match core::mem::replace(self, CompactMap::Heap(heap)) {
                    CompactMap::Heap(_) => unsafe { unreachable_unchecked() },
                    CompactMap::Inline(inline) => {
                        let heap = match self {
                            CompactMap::Heap(heap) => heap,
                            CompactMap::Inline(_) => unsafe { unreachable_unchecked() },
                        };
                        for (k, v) in inline.into_iter() {
                            unsafe { heap.insert_unique_unchecked(k, v); };
                        }
                        heap
                    }
                };
                heap.insert(key, value)
            }
        }
    }

    #[inline]
    pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V>
    where
        Q: Hash + Equivalent<K>,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.remove_entry(k) {
            Some((_, v)) => Some(v),
            None => None,
        }
    }

    #[inline]
    pub fn remove_entry<Q: ?Sized>(&mut self, k: &Q) -> Option<(K, V)>
    where
        Q: Hash + Equivalent<K>,
    {
        match self {
            CompactMap::Heap(inner) => inner.remove_entry(k),
            CompactMap::Inline(inner) => inner.remove_entry(k),
        }
    }
}

impl<K, V> CompactMap<K, V>{
    /// Clears the map.
    ///
    /// This method clears the map as resets it to the Inline state.
    ///
    /// # Examples
    ///
    /// ```
    /// use small_map::CompactMap;
    ///
    /// let mut map: CompactMap<i32, ()> = CompactMap::new();
    /// for i in 0..128 {
    ///     map.insert(i, ());
    /// }
    /// assert!(!map.is_inline());
    /// assert_eq!(map.len(), 128);
    ///
    /// map.clear();
    /// assert!(map.is_inline());
    /// assert_eq!(map.len(), 0);
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        *self = Self::Inline(Inline::new());
    }
}

pub enum Iter<'a, K, V> {
    Heap(hashbrown::hash_map::Iter<'a, K, V>),
    Inline(inline::Iter<'a, K, V>),
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        match self {
            Iter::Heap(inner) => inner.next(),
            Iter::Inline(inner) => inner.next(),
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            Iter::Heap(inner) => inner.size_hint(),
            Iter::Inline(inner) => inner.size_hint(),
        }
    }
}

impl<K, V> ExactSizeIterator for Iter<'_, K, V> {
    #[inline]
    fn len(&self) -> usize {
        match self {
            Iter::Heap(inner) => inner.len(),
            Iter::Inline(inner) => inner.len(),
        }
    }
}

pub enum IntoIter<K, V> {
    Heap(hashbrown::hash_map::IntoIter<K, V>),
    Inline(inline::IntoIter<K, V>),
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<(K, V)> {
        match self {
            IntoIter::Heap(inner) => inner.next(),
            IntoIter::Inline(inner) => inner.next(),
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            IntoIter::Heap(inner) => inner.size_hint(),
            IntoIter::Inline(inner) => inner.size_hint(),
        }
    }
}
impl<K, V> ExactSizeIterator for IntoIter<K, V> {
    #[inline]
    fn len(&self) -> usize {
        match self {
            IntoIter::Heap(inner) => inner.len(),
            IntoIter::Inline(inner) => inner.len(),
        }
    }
}
impl<K, V> FusedIterator for IntoIter<K, V> {}

impl<K, V> IntoIterator for CompactMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    /// Creates a consuming iterator, that is, one that moves each key-value
    /// pair out of the map in arbitrary order. The map cannot be used after
    /// calling this.
    #[inline]
    fn into_iter(self) -> IntoIter<K, V> {
        match self {
            CompactMap::Heap(inner) => IntoIter::Heap(inner.into_iter()),
            CompactMap::Inline(inner) => IntoIter::Inline(inner.into_iter()),
        }
    }
}

impl<'a, K, V> IntoIterator for &'a CompactMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    /// Creates an iterator over the entries of a `HashMap` in arbitrary order.
    /// The iterator element type is `(&'a K, &'a V)`.
    #[inline]
    fn into_iter(self) -> Iter<'a, K, V> {
        match self {
            CompactMap::Heap(inner) => Iter::Heap(inner.iter()),
            CompactMap::Inline(inner) => Iter::Inline(inner.iter()),
        }
    }
}

impl<K, V> CompactMap<K, V> {
    #[inline]
    pub fn len(&self) -> usize {
        match self {
            CompactMap::Heap(inner) => inner.len(),
            CompactMap::Inline(inner) => inner.len(),
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        match self {
            CompactMap::Heap(inner) => inner.is_empty(),
            CompactMap::Inline(inner) => inner.is_empty(),
        }
    }

    #[inline]
    pub fn iter(&self) -> Iter<'_, K, V> {
        match self {
            CompactMap::Heap(inner) => Iter::Heap(inner.iter()),
            CompactMap::Inline(inner) => Iter::Inline(inner.iter()),
        }
    }
}
