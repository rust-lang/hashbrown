use crate::scopeguard::guard;
use core::iter::FusedIterator;
use core::mem;
use core::mem::MaybeUninit;
use core::ops::Range;
use core::ptr;

/// Builder for incremental initialization of [`ArrayIter].
///
/// # Safety
///
/// All write accesses to this structure are unsafe and must maintain a correct
/// count of `initialized` elements.
pub(crate) struct ArrayIterBuilder<T, const N: usize> {
    /// The array to be initialized.
    array_mut: [MaybeUninit<T>; N],
    /// The number of items that have been initialized so far.
    initialized: usize,
}

impl<T, const N: usize> ArrayIterBuilder<T, N> {
    /// Creates new [`ArrayIterBuilder`].
    #[inline]
    pub(crate) fn new() -> Self {
        ArrayIterBuilder {
            // SAFETY: The `assume_init` is safe because the type we are claiming to have
            // initialized here is a bunch of `MaybeUninit`s, which do not require initialization.
            array_mut: unsafe { MaybeUninit::uninit().assume_init() },
            initialized: 0,
        }
    }

    /// Adds an item to the array and updates the initialized item counter.
    ///
    /// # Safety
    ///
    /// No more than `N` elements must be initialized.
    #[inline]
    pub(crate) unsafe fn push_unchecked(&mut self, item: T) {
        // SAFETY: If `initialized` was correct before and the caller does not
        // invoke this method more than `N` times then writes will be in-bounds
        // and slots will not be initialized more than once.
        self.array_mut
            .get_unchecked_mut(self.initialized)
            .write(item);
        self.initialized += 1;
    }

    /// Returns `true` if all elements have been initialized
    #[inline]
    pub(crate) fn is_initialized(&self) -> bool {
        self.initialized == N
    }

    /// Builds [`ArrayIter`] from [`ArrayIterBuilder`].
    #[inline]
    pub(crate) fn build(self) -> ArrayIter<T, N> {
        let initialized = 0..self.initialized;
        // SAFETY: We provide the number of elements that are guaranteed to be initialized
        unsafe { ArrayIter::new_unchecked(self.array_mut, initialized) }
    }
}

/// A by-value [array] iterator.
pub struct ArrayIter<T, const N: usize> {
    data: [MaybeUninit<T>; N],
    alive: Range<usize>,
}

impl<T, const N: usize> ArrayIter<T, N> {
    const DATA_NEEDS_DROP: bool = mem::needs_drop::<T>();

    /// Creates an iterator over the elements in a partially-initialized buffer.
    ///
    /// # Safety
    ///
    /// - The `buffer[initialized]` elements must all be initialized.
    /// - The range must be canonical, with `initialized.start <= initialized.end`.
    /// - The range must be in-bounds for the buffer, with `initialized.end <= N`.
    ///   (Like how indexing `[0][100..100]` fails despite the range being empty.)
    ///
    /// It's sound to have more elements initialized than mentioned, though that
    /// will most likely result in them being leaked.
    #[inline]
    const unsafe fn new_unchecked(buffer: [MaybeUninit<T>; N], initialized: Range<usize>) -> Self {
        // SAFETY: one of our safety conditions is that the range is canonical.
        Self {
            data: buffer,
            alive: initialized,
        }
    }

    /// Returns an immutable slice of all elements that have not been yielded yet.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        unsafe {
            // SAFETY: We know that all elements within `alive` are properly initialized.
            let slice = self.data.get_unchecked(self.alive.clone());
            // SAFETY: casting `slice` to a `*const [T]` is safe since the `slice` is initialized,
            // and `MaybeUninit` is guaranteed to have the same layout as `T`.
            // The pointer obtained is valid since it refers to memory owned by `slice` which is a
            // reference and thus guaranteed to be valid for reads.
            &*(slice as *const [MaybeUninit<T>] as *const [T])
        }
    }

    /// Returns a mutable slice of all elements that have not been yielded yet.
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe {
            // SAFETY: We know that all elements within `alive` are properly initialized.
            let slice = self.data.get_unchecked_mut(self.alive.clone());
            // SAFETY: casting `slice` to a `*mut [T]` is safe since the `slice` is initialized,
            // and `MaybeUninit` is guaranteed to have the same layout as `T`.
            // The pointer obtained is valid since it refers to memory owned by `slice` which is a
            // reference and thus guaranteed to be valid for reads and writes.
            &mut *(slice as *mut [MaybeUninit<T>] as *mut [T])
        }
    }

    /// Returns an [`ArrayIter`] of the same size as `self`, with function `f`
    /// applied to each element in order.
    pub fn convert<F, U>(self, mut f: F) -> ArrayIter<U, N>
    where
        F: FnMut(T) -> U,
    {
        let mut builder = ArrayIterBuilder::<U, N>::new();
        if ArrayIter::<U, N>::DATA_NEEDS_DROP {
            // Function may panic, in which case we need to make sure that we drop the elements
            // that have already been prodused.
            let mut guard = guard(&mut builder, |self_| {
                // SAFETY:
                // 1. The `slice` will contain only initialized objects;
                // 2. `MaybeUninit<U>` is guaranteed to have the same size, alignment, and ABI as U
                unsafe {
                    let slice: *mut [MaybeUninit<U>] =
                        self_.array_mut.get_unchecked_mut(..self_.initialized);
                    ptr::drop_in_place(slice as *mut [U]);
                }
            });

            for item in self {
                // SAFETY: `self` length is equal to `builder/guard` length
                unsafe { guard.push_unchecked(f(item)) }
            }
            mem::forget(guard);
        } else {
            for item in self {
                // SAFETY: `self` length is equal to `builder` length
                unsafe { builder.push_unchecked(f(item)) }
            }
        }

        builder.build()
    }
}

impl<T, const N: usize> Drop for ArrayIter<T, N> {
    fn drop(&mut self) {
        // SAFETY: This is safe: `as_mut_slice` returns exactly the sub-slice
        // of elements that have not been moved out yet and that remain
        // to be dropped.
        unsafe { ptr::drop_in_place(self.as_mut_slice()) }
    }
}

impl<T, const N: usize> Iterator for ArrayIter<T, N> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // Get the next index from the front.
        //
        // Increasing `alive.start` by 1 maintains the invariant regarding
        // `alive`. However, due to this change, for a short time, the alive
        // zone is not `data[alive]` anymore, but `data[idx..alive.end]`.
        //
        // Avoid `Option::unwrap_or_else` because it bloats LLVM IR.
        match self.alive.next() {
            Some(idx) => {
                // Read the element from the array.
                // SAFETY: `idx` is an index into the former "alive" region of the
                // array. Reading this element means that `data[idx]` is regarded as
                // dead now (i.e. do not touch). As `idx` was the start of the
                // alive-zone, the alive zone is now `data[alive]` again, restoring
                // all invariants.
                Some(unsafe { self.data.get_unchecked(idx).assume_init_read() })
            }
            None => None,
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }

    #[inline]
    fn fold<Acc, Fold>(mut self, init: Acc, mut fold: Fold) -> Acc
    where
        Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        let data = &mut self.data;
        self.alive.by_ref().fold(init, |acc, idx| {
            // SAFETY: idx is obtained by folding over the `alive` range, which implies the
            // value is currently considered alive but as the range is being consumed each value
            // we read here will only be read once and then considered dead.
            fold(acc, unsafe { data.get_unchecked(idx).assume_init_read() })
        })
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<T, const N: usize> DoubleEndedIterator for ArrayIter<T, N> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        // Get the next index from the back.
        //
        // Decreasing `alive.end` by 1 maintains the invariant regarding
        // `alive`. However, due to this change, for a short time, the alive
        // zone is not `data[alive]` anymore, but `data[alive.start..=idx]`.
        //
        // Avoid `Option::unwrap_or_else` because it bloats LLVM IR.
        match self.alive.next_back() {
            Some(idx) => {
                // Read the element from the array.
                // SAFETY: `idx` is an index into the former "alive" region of the
                // array. Reading this element means that `data[idx]` is regarded as
                // dead now (i.e. do not touch). As `idx` was the end of the
                // alive-zone, the alive zone is now `data[alive]` again, restoring
                // all invariants.
                Some(unsafe { self.data.get_unchecked(idx).assume_init_read() })
            }
            None => None,
        }
    }

    #[inline]
    fn rfold<Acc, Fold>(mut self, init: Acc, mut rfold: Fold) -> Acc
    where
        Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        let data = &mut self.data;
        self.alive.by_ref().rfold(init, |acc, idx| {
            // SAFETY: idx is obtained by folding over the `alive` range, which implies the
            // value is currently considered alive but as the range is being consumed each value
            // we read here will only be read once and then considered dead.
            rfold(acc, unsafe { data.get_unchecked(idx).assume_init_read() })
        })
    }
}

impl<T, const N: usize> ExactSizeIterator for ArrayIter<T, N> {
    #[inline]
    fn len(&self) -> usize {
        self.alive.len()
    }
}

impl<T, const N: usize> FusedIterator for ArrayIter<T, N> {}
