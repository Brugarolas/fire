use core::{iter::FusedIterator, mem::MaybeUninit, ptr::NonNull};

use super::RawIterInner;
use crate::helpers::compact_map::{inline::AlignedGroups, raw::util::Bucket};
use crate::helpers::compact_map::INLINE_CAPACITY;

pub(crate) struct RawIter<'a, T> {
    pub(crate) inner: RawIterInner<T>,
    pub(crate) aligned_groups: &'a AlignedGroups,
    pub(crate) data: &'a [MaybeUninit<T>; INLINE_CAPACITY],
}

impl<'a, T> Iterator for RawIter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        match self.inner.next(self.aligned_groups.as_ptr(), unsafe {
            Bucket::from_base_index(NonNull::new_unchecked(self.data.as_ptr() as _), 0)
        }) {
            Some(x) => unsafe {
                let r = x.as_ref();
                Some(r)
            },
            None => None,
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<T> ExactSizeIterator for RawIter<'_, T> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<T> FusedIterator for RawIter<'_, T> {}

pub(crate) struct RawIntoIter<T> {
    pub(crate) inner: RawIterInner<T>,
    pub(crate) aligned_groups: AlignedGroups,
    pub(crate) data: [MaybeUninit<T>; INLINE_CAPACITY],
}

impl<T> Iterator for RawIntoIter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        unsafe {
            Some(
                self.inner
                    .next(
                        self.aligned_groups.as_ptr(),
                        Bucket::from_base_index(NonNull::new_unchecked(self.data.as_ptr() as _), 0),
                    )?
                    .read(),
            )
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<T> ExactSizeIterator for RawIntoIter<T> {}
impl<T> FusedIterator for RawIntoIter<T> {}

impl<T> Drop for RawIntoIter<T> {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            // Drop all remaining elements
            self.inner.drop_elements(
                self.aligned_groups.as_ptr(),
                Bucket::from_base_index(NonNull::new_unchecked(self.data.as_ptr() as _), 0),
            );
        }
    }
}

pub(crate) struct RawIterMut<'a, T> {
    pub(crate) inner: RawIterInner<T>,
    pub(crate) aligned_groups: &'a AlignedGroups,
    pub(crate) data: &'a mut [MaybeUninit<T>; INLINE_CAPACITY],
}

impl<'a, T> Iterator for RawIterMut<'a, T> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            let base = Bucket::from_base_index(
                NonNull::new_unchecked(self.data.as_mut_ptr() as *mut _),
                0,
            );
            Some(self.inner.next(self.aligned_groups.as_ptr(), base)?.as_mut())
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<T> ExactSizeIterator for RawIterMut<'_, T> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<T> FusedIterator for RawIterMut<'_, T> {}
