// helpers/array.rs
//! A fixed-size array that can store elements of different types.
//! It uses type-level programming to keep track of the types and sizes of the elements.
//! It provides a way to push elements, iterate over them, and get their length.
//! It is implemented as a ZST (zero-sized type) with a byte array to store the data.
//! It uses traits to represent type-level lists and perform operations on them.

use std::marker::PhantomData;
use std::mem::size_of;

pub const fn size_of_val<T>(_: &T) -> usize {
    size_of::<T>()
}

// ZST
pub struct Node<V, N = Empty> {
    value: PhantomData<V>,
    next: PhantomData<N>,
}

#[repr(transparent)]
pub struct Array<const N: usize, F, B> {
    data: [u8; N], // Array of bytes
    forward: PhantomData<F>,
    backward: PhantomData<B>,
}

impl Array<0, Empty, Empty> {
    pub const fn new<const N: usize>() -> Array<N, Empty, Empty> {
        Array {
            data: [0; N],
            forward: PhantomData,
            backward: PhantomData,
        }
    }
}

impl<const N: usize, F: ArrayAppend + Length, B: MemorySize + RemoveFirst> Array<N, F, B> {
    pub fn push<V>(mut self, value: V) -> Array<N, F::Output<V>, Node<V, B>> {
        assert!(
            size_of::<V>() + B::SIZE <= N,
            "The element doesn't fit in the array"
        );
        // TODO: ChecK N is doesn't wrap around
        // TODO: Try to cast transmute self without moving it
        unsafe { self.data.as_mut_ptr().add(B::SIZE).cast::<V>().write(value) };
        let Array { data, .. } = self;

        Array {
            data,
            forward: PhantomData,
            backward: PhantomData,
        }
    }

    pub const fn forward(&self) -> RefIterator<'_, F, Empty, Self> {
        RefIterator::new_forward(self)
    }

    pub const fn backward(&self) -> RefIterator<'_, B::Element, B::Rest, Self> {
        RefIterator::new_backward(self)
    }

    pub const fn len(&self) -> usize {
        F::SIZE
    }

    pub const fn is_empty(&self) -> bool {
        F::SIZE == 0
    }
}

pub struct RefIterator<'a, CF, CB, A> {
    array: &'a A,
    current_foreward: PhantomData<CF>,
    current_backward: PhantomData<CB>,
}

impl RefIterator<'static, Empty, Empty, Empty> {
    const fn new_forward<const N: usize, F, B>(
        array: &Array<N, F, B>,
    ) -> RefIterator<'_, F, Empty, Array<N, F, B>> {
        RefIterator {
            array,
            current_foreward: PhantomData,
            current_backward: PhantomData,
        }
    }

    const fn new_backward<const N: usize, F, B: RemoveFirst>(
        array: &Array<N, F, B>,
    ) -> RefIterator<'_, B::Element, B::Rest, Array<N, F, B>> {
        RefIterator {
            array,
            current_foreward: PhantomData,
            current_backward: PhantomData,
        }
    }
}

impl<'a, A, CFV, CFN: NotEmpty, CB> RefIterator<'a, Node<CFV, CFN>, CB, A> {
    pub const fn next(self) -> RefIterator<'a, CFN, Node<CFV, CB>, A> {
        let RefIterator { array, .. } = self;

        RefIterator {
            array,
            current_foreward: PhantomData,
            current_backward: PhantomData,
        }
    }
}

impl<'a, A, CF, CBV, CBN> RefIterator<'a, CF, Node<CBV, CBN>, A> {
    pub const fn prev(self) -> RefIterator<'a, Node<CBV, CF>, CBN, A> {
        let RefIterator { array, .. } = self;

        RefIterator {
            array,
            current_foreward: PhantomData,
            current_backward: PhantomData,
        }
    }
}
impl<'a, const N: usize, F, B, CFV, CFN, CB: MemorySize>
    RefIterator<'a, Node<CFV, CFN>, CB, Array<N, F, B>>
{
    pub const fn index(&self) -> usize {
        CB::SIZE
    }

    pub fn value(&self) -> &CFV {
        unsafe {
            // TODO: Find a way to fix unaligned error
            self.array
                .data
                .as_ptr()
                .add(self.index())
                .cast::<CFV>()
                .as_ref()
                .unwrap_unchecked()
        }
    }
}

impl<'a, const N: usize, F, B: RemoveFirst, CFV, CFN, CB: MemorySize>
    RefIterator<'a, Node<CFV, CFN>, CB, Array<N, F, B>>
{
    pub const fn forward(self) -> RefIterator<'a, F, Empty, Array<N, F, B>> {
        RefIterator::new_forward(self.array)
    }

    pub const fn backward(self) -> RefIterator<'a, B::Element, B::Rest, Array<N, F, B>> {
        RefIterator::new_backward(self.array)
    }
}

#[macro_export]
macro_rules! array {
    ($($x:expr),+ $(,)?) => {{
        const N: usize = 0 $(+ $crate::array::size_of_val(&$x))+;
        Array::new::<N>()$(.push($x))+
    }};
}

// =================== Traits ===================

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Empty;

pub trait NotEmpty {}

pub trait Length {
    const SIZE: usize = 0;

    fn len(&self) -> usize {
        Self::SIZE
    }

    fn is_empty(&self) -> bool {
        Self::SIZE == 0
    }
}
impl Length for Empty {}

pub trait Index<I> {
    type Output<'a>
    where
        Self: 'a;

    fn index(&self) -> Self::Output<'_>;
}

pub trait ArrayAppend {
    type Output<T>;
}
impl ArrayAppend for Empty {
    type Output<T> = Node<T>;
}
impl<V, N: ArrayAppend> ArrayAppend for Node<V, N> {
    type Output<T> = Node<V, N::Output<T>>;
}

pub trait MemorySize {
    const SIZE: usize = 0;
}
impl MemorySize for Empty {}
impl<V, N: MemorySize> MemorySize for Node<V, N> {
    const SIZE: usize = size_of::<V>() + N::SIZE;
}

pub trait RemoveFirst {
    type Element;
    type Rest;
}
impl RemoveFirst for Empty {
    type Element = Empty;
    type Rest = Empty;
}
impl<V, N> RemoveFirst for Node<V, N> {
    type Element = Node<V>;
    type Rest = N;
}

impl<V> NotEmpty for Node<V> {}
impl<V, N: NotEmpty> NotEmpty for Node<V, N> {}

impl<V, N: Length> Length for Node<V, N> {
    const SIZE: usize = 1 + N::SIZE;
}