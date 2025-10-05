use crate::helpers::compact_map::INLINE_CAPACITY;
use crate::helpers::compact_map::AesBuildHasher;
use crate::helpers::compact_map::raw::iter::RawIterMut;

use core::{
    hash::{BuildHasher, Hash},
    iter::FusedIterator,
    mem::{self, transmute, MaybeUninit},
    ptr::NonNull,
};

use crate::helpers::compact_map::{
    raw::{
        h2,
        iter::{RawIntoIter, RawIter},
        util::{equivalent_key, likely, make_hash, Bucket, InsertSlot, SizedTypeProperties},
        BitMaskWord, Group, RawIterInner, DELETED, EMPTY,
    },
    Equivalent,
};

#[derive(Clone)]
pub struct Inline<K, V> {
    raw: RawInline<(K, V)>,
    hash_builder: AesBuildHasher,
}

impl<K, V> Default for Inline<K, V> {
    #[inline]
    fn default() -> Self {
        Self {
            raw: RawInline::default(),
            hash_builder: AesBuildHasher::default(),
        }
    }
}

struct RawInline<T> {
    aligned_groups: AlignedGroups,
    len: usize,
    data: [MaybeUninit<T>; INLINE_CAPACITY],
}

impl<T: Clone> Clone for RawInline<T> {
    #[inline]
    fn clone(&self) -> Self {
        let mut data: [MaybeUninit<T>; INLINE_CAPACITY] =
            unsafe { MaybeUninit::uninit().assume_init() };

        // Copy only buckets that are really full (not EMPTY/DELETED).
        for i in 0..INLINE_CAPACITY {
            let ctrl = unsafe { *self.aligned_groups.ctrl(i) };
            if ctrl != EMPTY && ctrl != DELETED {
                unsafe {
                    let src = self.data.get_unchecked(i).assume_init_ref();
                    data[i] = MaybeUninit::new(src.clone());
                }
            }
        }

        Self {
            aligned_groups: self.aligned_groups,
            len: self.len,
            data,
        }
    }
}

impl<T> Default for RawInline<T> {
    #[inline]
    fn default() -> Self {
        Self {
            aligned_groups: AlignedGroups {
                groups: [EMPTY; INLINE_CAPACITY],
                _align: [],
            },
            len: 0,
            data: unsafe { MaybeUninit::<[MaybeUninit<T>; INLINE_CAPACITY]>::uninit().assume_init() },
        }
    }
}

impl<T> RawInline<T> {
    pub fn new() -> Self {
        Self::default()
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct AlignedGroups {
    groups: [u8; INLINE_CAPACITY],
    _align: [Group; 0],
}

impl AlignedGroups {
    #[inline]
    unsafe fn ctrl(&self, index: usize) -> *mut u8 {
        self.groups.as_ptr().add(index).cast_mut()
    }

    #[inline]
    pub(crate) fn as_ptr(&self) -> NonNull<u8> {
        unsafe { NonNull::new_unchecked(self.groups.as_ptr() as _) }
    }
}

impl<T> Drop for RawInline<T> {
    #[inline]
    fn drop(&mut self) {
        unsafe { self.drop_elements() }
    }
}

impl<T> RawInline<T> {
    #[inline]
    unsafe fn drop_elements(&mut self) {
        if T::NEEDS_DROP && self.len != 0 {
            unsafe {
                drop(RawIntoIter {
                    inner: self.raw_iter_inner(),
                    aligned_groups: (&self.aligned_groups as *const AlignedGroups).read(),
                    data: (&self.data as *const [MaybeUninit<T>; INLINE_CAPACITY]).read(),
                });
            }
        }
    }

    /// Gets a reference to an element in the table.
    #[inline]
    fn get(&self, hash: u64, eq: impl FnMut(&T) -> bool) -> Option<&T> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.find(hash, eq) {
            Some(bucket) => Some(unsafe { bucket.as_ref() }),
            None => None,
        }
    }

    /// Gets a mutable reference to an element in the table.
    #[inline]
    fn get_mut(&mut self, hash: u64, eq: impl FnMut(&T) -> bool) -> Option<&mut T> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.find(hash, eq) {
            Some(bucket) => Some(unsafe { bucket.as_mut() }),
            None => None,
        }
    }

    const UNCHECKED_GROUP: usize = 64 / Group::WIDTH;
    const TAIL_MASK: BitMaskWord = Group::LOWEST_MASK[64 % Group::WIDTH];

    /// Searches for an element in the table.
    #[inline]
    fn find(&self, hash: u64, mut eq: impl FnMut(&T) -> bool) -> Option<Bucket<T>> {
        unsafe {
            let h2_hash = h2(hash);
            let mut probe_pos = 0;

            // Manually expand the loop
            for _ in 0..Self::UNCHECKED_GROUP {
                let group = Group::load(self.aligned_groups.ctrl(probe_pos));
                let matches = group.match_byte(h2_hash);
                for bit in matches {
                    let index = probe_pos + bit;
                    if likely(eq(self.data.get_unchecked(index).assume_init_ref())) {
                        return Some(self.bucket(index));
                    }
                }
                probe_pos += Group::WIDTH;
            }
            if INLINE_CAPACITY % Group::WIDTH != 0 {
                let group = Group::load(self.aligned_groups.ctrl(probe_pos));
                // Clear invalid tail.
                let matches = group.match_byte(h2_hash).and(Self::TAIL_MASK);
                for bit in matches {
                    let index = probe_pos + bit;
                    if likely(eq(self.data.get_unchecked(index).assume_init_ref())) {
                        return Some(self.bucket(index));
                    }
                }
            }
            None
        }
    }

    /// Searches for an element in the table. If the element is not found,
    /// returns `Err` with the position of a slot where an element with the
    /// same hash could be inserted.
    #[inline]
    fn find_or_find_insert_slot(
        &mut self,
        hash: u64,
        mut eq: impl FnMut(&T) -> bool,
    ) -> Result<Bucket<T>, InsertSlot> {
        unsafe {
            let mut insert_slot = None;
            let h2_hash = h2(hash);
            let mut probe_pos = 0;

            // Manually expand the loop
            for _ in 0..Self::UNCHECKED_GROUP {
                let group = Group::load(self.aligned_groups.ctrl(probe_pos));
                let matches = group.match_byte(h2_hash);
                for bit in matches {
                    let index = probe_pos + bit;
                    if likely(eq(self.data.get_unchecked(index).assume_init_ref())) {
                        return Ok(self.bucket(index));
                    }
                }

                // We didn't find the element we were looking for in the group, try to get an
                // insertion slot from the group if we don't have one yet.
                if likely(insert_slot.is_none()) {
                    insert_slot = self.find_insert_slot_in_group(&group, probe_pos);
                }

                // If there's empty set, we should stop searching next group.
                if likely(group.match_empty().any_bit_set()) {
                    break;
                }
                probe_pos += Group::WIDTH;
            }
            if INLINE_CAPACITY % Group::WIDTH != 0 {
                let group = Group::load(self.aligned_groups.ctrl(probe_pos));
                let matches = group.match_byte(h2_hash).and(Self::TAIL_MASK);
                for bit in matches {
                    let index = probe_pos + bit;
                    if likely(eq(self.data.get_unchecked(index).assume_init_ref())) {
                        return Ok(self.bucket(index));
                    }
                }

                // We didn't find the element we were looking for in the group, try to get an
                // insertion slot from the group if we don't have one yet.
                if likely(insert_slot.is_none()) {
                    insert_slot = self.find_insert_slot_in_group(&group, probe_pos);
                }
            }

            Err(InsertSlot {
                index: insert_slot.unwrap_unchecked(),
            })
        }
    }

    /// Finds the position to insert something in a group.
    #[inline]
    fn find_insert_slot_in_group(&self, group: &Group, probe_seq: usize) -> Option<usize> {
        let bit = group.match_empty_or_deleted().lowest_set_bit();

        if likely(bit.is_some()) {
            let n = unsafe { bit.unwrap_unchecked() };
            return Some(probe_seq + n);
        }
        None
    }

    /// Inserts a new element into the table in the given slot, and returns its
    /// raw bucket.
    #[inline]
    unsafe fn insert_in_slot(&mut self, hash: u64, slot: InsertSlot, value: T) -> Bucket<T> {
        self.record_item_insert_at(slot.index, hash);
        let bucket = self.bucket(slot.index);
        bucket.write(value);
        bucket
    }

    /// Inserts a new element into the table in the given slot, and returns its
    /// raw bucket.
    #[inline]
    unsafe fn record_item_insert_at(&mut self, index: usize, hash: u64) {
        self.set_ctrl_h2(index, hash);
        self.len += 1;
    }

    /// Sets a control byte to the hash, and possibly also the replicated control byte at
    /// the end of the array.
    #[inline]
    unsafe fn set_ctrl_h2(&mut self, index: usize, hash: u64) {
        // SAFETY: The caller must uphold the safety rules for the [`RawTableInner::set_ctrl_h2`]
        *self.aligned_groups.ctrl(index) = h2(hash);
    }

    /// Finds and removes an element from the table, returning it.
    #[inline]
    fn remove_entry(&mut self, hash: u64, eq: impl FnMut(&T) -> bool) -> Option<T> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.find(hash, eq) {
            Some(bucket) => Some(unsafe { self.remove(bucket).0 }),
            None => None,
        }
    }

    /// Removes an element from the table, returning it.
    #[inline]
    #[allow(clippy::needless_pass_by_value)]
    unsafe fn remove(&mut self, item: Bucket<T>) -> (T, InsertSlot) {
        self.erase_no_drop(&item);
        (
            item.read(),
            InsertSlot {
                index: self.bucket_index(&item),
            },
        )
    }

    /// Erases an element from the table without dropping it.
    #[inline]
    unsafe fn erase_no_drop(&mut self, item: &Bucket<T>) {
        let index = self.bucket_index(item);
        self.erase(index);
    }

    /// Returns the index of a bucket from a `Bucket`.
    #[inline]
    unsafe fn bucket_index(&self, bucket: &Bucket<T>) -> usize {
        bucket.to_base_index(NonNull::new_unchecked(self.data.as_ptr() as _))
    }

    /// Erases the [`Bucket`]'s control byte at the given index so that it does not
    /// triggered as full, decreases the `items` of the table and, if it can be done,
    /// increases `self.growth_left`.
    #[inline]
    unsafe fn erase(&mut self, index: usize) {
        *self.aligned_groups.ctrl(index) = DELETED;
        self.len -= 1;
    }

    /// Returns a pointer to an element in the table.
    #[inline]
    unsafe fn bucket(&self, index: usize) -> Bucket<T> {
        Bucket::from_base_index(
            NonNull::new_unchecked(transmute(self.data.as_ptr().cast_mut())),
            index,
        )
    }

    #[inline]
    unsafe fn raw_iter_inner(&self) -> RawIterInner<T> {
        let init_group = Group::load_aligned(self.aligned_groups.ctrl(0)).match_full();
        RawIterInner::new(init_group, self.len)
    }

    #[inline]
    fn iter(&self) -> RawIter<'_, T> {
        RawIter {
            inner: unsafe { self.raw_iter_inner() },
            aligned_groups: &self.aligned_groups,
            data: &self.data,
        }
    }
}

impl<T> IntoIterator for RawInline<T> {
    type Item = T;
    type IntoIter = RawIntoIter<T>;

    #[inline]
    fn into_iter(self) -> RawIntoIter<T> {
        let ret = unsafe {
            RawIntoIter {
                inner: self.raw_iter_inner(),
                aligned_groups: (&self.aligned_groups as *const AlignedGroups).read(),
                data: (&self.data as *const [MaybeUninit<T>; INLINE_CAPACITY]).read(),
            }
        };
        mem::forget(self);
        ret
    }
}

pub struct Iter<'a, K, V> {
    inner: RawIter<'a, (K, V)>,
}

pub struct IntoIter<K, V> {
    inner: RawIntoIter<(K, V)>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        match self.inner.next() {
            Some(kv) => Some((&kv.0, &kv.1)),
            None => None,
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<(K, V)> {
        self.inner.next()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}
impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<K, V> ExactSizeIterator for IntoIter<K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<'a, K, V> FusedIterator for Iter<'a, K, V> {}
impl<K, V> FusedIterator for IntoIter<K, V> {}

impl<K, V> IntoIterator for Inline<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.raw.into_iter(),
        }
    }
}

impl<K, V> Inline<K, V> {
    #[inline]
    pub(crate) fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            inner: self.raw.iter(),
        }
    }

    #[inline]
    pub(crate) fn new() -> Self {
        Self {
            raw: RawInline {
                aligned_groups: AlignedGroups {
                    groups: [EMPTY; INLINE_CAPACITY],
                    _align: [],
                },
                len: 0,

                data: unsafe { MaybeUninit::<[MaybeUninit<(K, V)>; INLINE_CAPACITY]>::uninit().assume_init() },
            },
            hash_builder: AesBuildHasher::default(),
        }
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.raw.len == 0
    }

    #[inline]
    pub(crate) fn is_full(&self) -> bool {
        self.raw.len == INLINE_CAPACITY
    }

    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.raw.len
    }

    // # Safety
    // Hasher must exist.
    #[inline]
    pub(crate) unsafe fn take_hasher(&mut self) -> AesBuildHasher {
        self.hash_builder
    }

    #[inline]
    fn hash_builder(&self) -> &AesBuildHasher {
        &self.hash_builder
    }
}

impl<K, V> Inline<K, V>
where
    K: Eq + Hash,
{
    /// Returns a reference to the value corresponding to the key.
    #[inline]
    pub(crate) fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where
        Q: Hash + Equivalent<K>,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.get_inner(k) {
            Some((_, v)) => Some(v),
            None => None,
        }
    }

    /// Returns a reference to the value corresponding to the key.
    #[inline]
    pub(crate) fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V>
    where
        Q: Hash + Equivalent<K>,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.get_inner_mut(k) {
            Some((_, v)) => Some(v),
            None => None,
        }
    }

    /// Returns the key-value pair corresponding to the supplied key.
    #[inline]
    pub(crate) fn get_key_value<Q: ?Sized>(&self, k: &Q) -> Option<(&K, &V)>
    where
        Q: Hash + Equivalent<K>,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.get_inner(k) {
            Some((key, value)) => Some((key, value)),
            None => None,
        }
    }

    /// Inserts a key-value pair into the map.
    #[inline]
    pub(crate) fn insert(&mut self, k: K, v: V) -> Option<V> {
        let hash = make_hash::<K>(self.hash_builder(), &k);
        match self.raw.find_or_find_insert_slot(hash, equivalent_key(&k)) {
            Ok(bucket) => Some(mem::replace(unsafe { &mut bucket.as_mut().1 }, v)),
            Err(slot) => {
                unsafe {
                    self.raw.insert_in_slot(hash, slot, (k, v));
                }
                None
            }
        }
    }

    /// Removes a key from the map, returning the stored key and value if the
    /// key was previously in the map. Keeps the allocated memory for reuse.
    #[inline]
    pub(crate) fn remove_entry<Q: ?Sized>(&mut self, k: &Q) -> Option<(K, V)>
    where
        Q: Hash + Equivalent<K>,
    {
        let hash = make_hash::<Q>(self.hash_builder(), k);
        self.raw.remove_entry(hash, equivalent_key(k))
    }

    #[inline]
    fn get_inner<Q: ?Sized>(&self, k: &Q) -> Option<&(K, V)>
    where
        Q: Hash + Equivalent<K>,
    {
        if self.is_empty() {
            None
        } else {
            let hash = make_hash::<Q>(self.hash_builder(), k);
            self.raw.get(hash, equivalent_key(k))
        }
    }

    #[inline]
    fn get_inner_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut (K, V)>
    where
        Q: Hash + Equivalent<K>,
    {
        if self.is_empty() {
            None
        } else {
            let hash = make_hash::<Q>(self.hash_builder(), k);
            self.raw.get_mut(hash, equivalent_key(k))
        }
    }
}

pub struct IterMut<'a, K, V> {
    inner: RawIterMut<'a, (K, V)>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let kv: &mut (K, V) = self.inner.next()?;
        let k: &K = unsafe { &*(&kv.0 as *const K) };
        let v: &mut V = unsafe { &mut *(&mut kv.1 as *mut V) };
        Some((k, v))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K, V> ExactSizeIterator for IterMut<'a, K, V> {
    #[inline]
    fn len(&self) -> usize { self.inner.len() }
}
impl<'a, K, V> FusedIterator for IterMut<'a, K, V> {}

impl<K, V> Inline<K, V> {
    #[inline]
    pub(crate) fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut {
            inner: RawIterMut {
                inner: unsafe { self.raw.raw_iter_inner() },
                aligned_groups: &self.raw.aligned_groups,
                data: &mut self.raw.data,
            },
        }
    }
}
