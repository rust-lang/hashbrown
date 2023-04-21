use crate::alloc::alloc::{handle_alloc_error, Layout};
use crate::scopeguard::{guard, ScopeGuard};
use crate::TryReserveError;
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::mem;
use core::mem::ManuallyDrop;
use core::mem::MaybeUninit;
use core::ptr::NonNull;
use core::{hint, ptr};

cfg_if! {
    // Use the SSE2 implementation if possible: it allows us to scan 16 buckets
    // at once instead of 8. We don't bother with AVX since it would require
    // runtime dispatch and wouldn't gain us much anyways: the probability of
    // finding a match drops off drastically after the first few buckets.
    //
    // I attempted an implementation on ARM using NEON instructions, but it
    // turns out that most NEON instructions have multi-cycle latency, which in
    // the end outweighs any gains over the generic implementation.
    if #[cfg(all(
        target_feature = "sse2",
        any(target_arch = "x86", target_arch = "x86_64"),
        not(miri)
    ))] {
        mod sse2;
        use sse2 as imp;
    } else {
        #[path = "generic.rs"]
        mod generic;
        use generic as imp;
    }
}

mod alloc;
pub(crate) use self::alloc::{do_alloc, Allocator, Global};

mod bitmask;

use self::bitmask::{BitMask, BitMaskIter};
use self::imp::Group;

// Branch prediction hint. This is currently only available on nightly but it
// consistently improves performance by 10-15%.
#[cfg(feature = "nightly")]
use core::intrinsics::{likely, unlikely};

// On stable we can use #[cold] to get a equivalent effect: this attributes
// suggests that the function is unlikely to be called
#[cfg(not(feature = "nightly"))]
#[inline]
#[cold]
fn cold() {}

#[cfg(not(feature = "nightly"))]
#[inline]
fn likely(b: bool) -> bool {
    if !b {
        cold();
    }
    b
}
#[cfg(not(feature = "nightly"))]
#[inline]
fn unlikely(b: bool) -> bool {
    if b {
        cold();
    }
    b
}

// Use strict provenance functions if available.
#[cfg(feature = "nightly")]
use core::ptr::invalid_mut;
// Implement it with a cast otherwise.
#[cfg(not(feature = "nightly"))]
#[inline(always)]
fn invalid_mut<T>(addr: usize) -> *mut T {
    addr as *mut T
}

#[inline]
unsafe fn offset_from<T>(to: *const T, from: *const T) -> usize {
    to.offset_from(from) as usize
}

/// Whether memory allocation errors should return an error or abort.
#[derive(Copy, Clone)]
enum Fallibility {
    Fallible,
    Infallible,
}

impl Fallibility {
    /// Error to return on capacity overflow.
    #[cfg_attr(feature = "inline-more", inline)]
    fn capacity_overflow(self) -> TryReserveError {
        match self {
            Fallibility::Fallible => TryReserveError::CapacityOverflow,
            Fallibility::Infallible => panic!("Hash table capacity overflow"),
        }
    }

    /// Error to return on allocation error.
    #[cfg_attr(feature = "inline-more", inline)]
    fn alloc_err(self, layout: Layout) -> TryReserveError {
        match self {
            Fallibility::Fallible => TryReserveError::AllocError { layout },
            Fallibility::Infallible => handle_alloc_error(layout),
        }
    }
}

/// Control byte value for an empty bucket.
const EMPTY: u8 = 0b1111_1111;

/// Control byte value for a deleted bucket.
const DELETED: u8 = 0b1000_0000;

/// Checks whether a control byte represents a full bucket (top bit is clear).
#[inline]
fn is_full(ctrl: u8) -> bool {
    ctrl & 0x80 == 0
}

/// Checks whether a control byte represents a special value (top bit is set).
#[inline]
fn is_special(ctrl: u8) -> bool {
    ctrl & 0x80 != 0
}

/// Checks whether a special control value is EMPTY (just check 1 bit).
#[inline]
fn special_is_empty(ctrl: u8) -> bool {
    debug_assert!(is_special(ctrl));
    ctrl & 0x01 != 0
}

/// Primary hash function, used to select the initial bucket to probe from.
#[inline]
#[allow(clippy::cast_possible_truncation)]
fn h1(hash: u64) -> usize {
    // On 32-bit platforms we simply ignore the higher hash bits.
    hash as usize
}

// Constant for h2 function that grabing the top 7 bits of the hash.
const MIN_HASH_LEN: usize = if mem::size_of::<usize>() < mem::size_of::<u64>() {
    mem::size_of::<usize>()
} else {
    mem::size_of::<u64>()
};

/// Secondary hash function, saved in the low 7 bits of the control byte.
#[inline]
#[allow(clippy::cast_possible_truncation)]
fn h2(hash: u64) -> u8 {
    // Grab the top 7 bits of the hash. While the hash is normally a full 64-bit
    // value, some hash functions (such as FxHash) produce a usize result
    // instead, which means that the top 32 bits are 0 on 32-bit platforms.
    // So we use MIN_HASH_LEN constant to handle this.
    let top7 = hash >> (MIN_HASH_LEN * 8 - 7);
    (top7 & 0x7f) as u8 // truncation
}

/// Probe sequence based on triangular numbers, which is guaranteed (since our
/// table size is a power of two) to visit every group of elements exactly once.
///
/// A triangular probe has us jump by 1 more group every time. So first we
/// jump by 1 group (meaning we just continue our linear scan), then 2 groups
/// (skipping over 1 group), then 3 groups (skipping over 2 groups), and so on.
///
/// Proof that the probe will visit every group in the table:
/// <https://fgiesen.wordpress.com/2015/02/22/triangular-numbers-mod-2n/>
struct ProbeSeq {
    pos: usize,
    stride: usize,
}

impl ProbeSeq {
    #[inline]
    fn move_next(&mut self, bucket_mask: usize) {
        // We should have found an empty bucket by now and ended the probe.
        debug_assert!(
            self.stride <= bucket_mask,
            "Went past end of probe sequence"
        );

        self.stride += Group::WIDTH;
        self.pos += self.stride;
        self.pos &= bucket_mask;
    }
}

/// Returns the number of buckets needed to hold the given number of items,
/// taking the maximum load factor into account.
///
/// Returns `None` if an overflow occurs.
// Workaround for emscripten bug emscripten-core/emscripten-fastcomp#258
#[cfg_attr(target_os = "emscripten", inline(never))]
#[cfg_attr(not(target_os = "emscripten"), inline)]
fn capacity_to_buckets(cap: usize) -> Option<usize> {
    debug_assert_ne!(cap, 0);

    // For small tables we require at least 1 empty bucket so that lookups are
    // guaranteed to terminate if an element doesn't exist in the table.
    if cap < 8 {
        // We don't bother with a table size of 2 buckets since that can only
        // hold a single element. Instead we skip directly to a 4 bucket table
        // which can hold 3 elements.
        return Some(if cap < 4 { 4 } else { 8 });
    }

    // Otherwise require 1/8 buckets to be empty (87.5% load)
    //
    // Be careful when modifying this, calculate_layout relies on the
    // overflow check here.
    let adjusted_cap = cap.checked_mul(8)? / 7;

    // Any overflows will have been caught by the checked_mul. Also, any
    // rounding errors from the division above will be cleaned up by
    // next_power_of_two (which can't overflow because of the previous division).
    Some(adjusted_cap.next_power_of_two())
}

/// Returns the maximum effective capacity for the given bucket mask, taking
/// the maximum load factor into account.
#[inline]
fn bucket_mask_to_capacity(bucket_mask: usize) -> usize {
    if bucket_mask < 8 {
        // For tables with 1/2/4/8 buckets, we always reserve one empty slot.
        // Keep in mind that the bucket mask is one less than the bucket count.
        bucket_mask
    } else {
        // For larger tables we reserve 12.5% of the slots as empty.
        ((bucket_mask + 1) / 8) * 7
    }
}

/// Helper which allows the max calculation for ctrl_align to be statically computed for each T
/// while keeping the rest of `calculate_layout_for` independent of `T`
#[derive(Copy, Clone)]
struct TableLayout {
    size: usize,
    ctrl_align: usize,
}

impl TableLayout {
    #[inline]
    const fn new<T>() -> Self {
        let layout = Layout::new::<T>();
        Self {
            size: layout.size(),
            ctrl_align: if layout.align() > Group::WIDTH {
                layout.align()
            } else {
                Group::WIDTH
            },
        }
    }

    #[inline]
    fn calculate_layout_for(self, buckets: usize) -> Option<(Layout, usize)> {
        debug_assert!(buckets.is_power_of_two());

        let TableLayout { size, ctrl_align } = self;
        // Manual layout calculation since Layout methods are not yet stable.
        let ctrl_offset =
            size.checked_mul(buckets)?.checked_add(ctrl_align - 1)? & !(ctrl_align - 1);
        let len = ctrl_offset.checked_add(buckets + Group::WIDTH)?;

        // We need an additional check to ensure that the allocation doesn't
        // exceed `isize::MAX` (https://github.com/rust-lang/rust/pull/95295).
        if len > isize::MAX as usize - (ctrl_align - 1) {
            return None;
        }

        Some((
            unsafe { Layout::from_size_align_unchecked(len, ctrl_align) },
            ctrl_offset,
        ))
    }
}

/// A reference to a hash table bucket containing a `T`.
///
/// This is usually just a pointer to the element itself. However if the element
/// is a ZST, then we instead track the index of the element in the table so
/// that `erase` works properly.
pub struct Bucket<T> {
    // Actually it is pointer to next element than element itself
    // this is needed to maintain pointer arithmetic invariants
    // keeping direct pointer to element introduces difficulty.
    // Using `NonNull` for variance and niche layout
    ptr: NonNull<T>,
}

// This Send impl is needed for rayon support. This is safe since Bucket is
// never exposed in a public API.
unsafe impl<T> Send for Bucket<T> {}

impl<T> Clone for Bucket<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self { ptr: self.ptr }
    }
}

impl<T> Bucket<T> {
    const IS_ZERO_SIZED_TYPE: bool = mem::size_of::<T>() == 0;

    /// Creates a [`Bucket`] that contain pointer to the data.
    /// The pointer calculation is performed by calculating the
    /// offset from given `base` pointer (convenience for
    /// `base.as_ptr().sub(index)`).
    ///
    /// `index` is in units of `T`; e.g., an `index` of 3 represents a pointer
    /// offset of `3 * size_of::<T>()` bytes.
    ///
    /// If the `T` is a ZST, then we instead track the index of the element
    /// in the table so that `erase` works properly (return
    /// `NonNull::new_unchecked((index + 1) as *mut T)`)
    ///
    /// # Safety
    ///
    /// If `mem::size_of::<T>() != 0`, then the safety rules are directly derived
    /// from the safety rules for [`<*mut T>::sub`] method of `*mut T` and the safety
    /// rules of [`NonNull::new_unchecked`] function.
    ///
    /// Thus, in order to uphold the safety contracts for the [`<*mut T>::sub`] method
    /// and [`NonNull::new_unchecked`] function, as well as for the correct
    /// logic of the work of this crate, the following rules are necessary and
    /// sufficient:
    ///
    /// * the `base` pointer must not be `dangling` and must points to the
    ///   end of the first `value element` from the `data part` of the table, i.e.
    ///   must be the pointer that returned by [`RawTable::data_end`] or by
    ///   [`RawTableInner::data_end<T>`];
    ///
    /// * `index` must not be greater than `RawTableInner.bucket_mask`, i.e.
    ///   `index <= RawTableInner.bucket_mask` or, in other words, `(index + 1)`
    ///   must be no greater than the number returned by the function
    ///   [`RawTable::buckets`] or [`RawTableInner::buckets`].
    ///
    /// If `mem::size_of::<T>() == 0`, then the only requirement is that the
    /// `index` must not be greater than `RawTableInner.bucket_mask`, i.e.
    /// `index <= RawTableInner.bucket_mask` or, in other words, `(index + 1)`
    /// must be no greater than the number returned by the function
    /// [`RawTable::buckets`] or [`RawTableInner::buckets`].
    ///
    /// [`Bucket`]: crate::raw::Bucket
    /// [`<*mut T>::sub`]: https://doc.rust-lang.org/core/primitive.pointer.html#method.sub-1
    /// [`NonNull::new_unchecked`]: https://doc.rust-lang.org/stable/std/ptr/struct.NonNull.html#method.new_unchecked
    /// [`RawTable::data_end`]: crate::raw::RawTable::data_end
    /// [`RawTableInner::data_end<T>`]: RawTableInner::data_end<T>
    /// [`RawTable::buckets`]: crate::raw::RawTable::buckets
    /// [`RawTableInner::buckets`]: RawTableInner::buckets
    #[inline]
    unsafe fn from_base_index(base: NonNull<T>, index: usize) -> Self {
        // If mem::size_of::<T>() != 0 then return a pointer to an `element` in
        // the data part of the table (we start counting from "0", so that
        // in the expression T[last], the "last" index actually one less than the
        // "buckets" number in the table, i.e. "last = RawTableInner.bucket_mask"):
        //
        //                   `from_base_index(base, 1).as_ptr()` returns a pointer that
        //                   points here in the data part of the table
        //                   (to the start of T1)
        //                        |
        //                        |        `base: NonNull<T>` must point here
        //                        |         (to the end of T0 or to the start of C0)
        //                        v         v
        // [Padding], Tlast, ..., |T1|, T0, |C0, C1, ..., Clast
        //                           ^
        //                           `from_base_index(base, 1)` returns a pointer
        //                           that points here in the data part of the table
        //                           (to the end of T1)
        //
        // where: T0...Tlast - our stored data; C0...Clast - control bytes
        // or metadata for data.
        let ptr = if Self::IS_ZERO_SIZED_TYPE {
            // won't overflow because index must be less than length (bucket_mask)
            // and bucket_mask is guaranteed to be less than `isize::MAX`
            // (see TableLayout::calculate_layout_for method)
            invalid_mut(index + 1)
        } else {
            base.as_ptr().sub(index)
        };
        Self {
            ptr: NonNull::new_unchecked(ptr),
        }
    }

    /// Calculates the index of a [`Bucket`] as distance between two pointers
    /// (convenience for `base.as_ptr().offset_from(self.ptr.as_ptr()) as usize`).
    /// The returned value is in units of T: the distance in bytes divided by
    /// [`core::mem::size_of::<T>()`].
    ///
    /// If the `T` is a ZST, then we return the index of the element in
    /// the table so that `erase` works properly (return `self.ptr.as_ptr() as usize - 1`).
    ///
    /// This function is the inverse of [`from_base_index`].
    ///
    /// # Safety
    ///
    /// If `mem::size_of::<T>() != 0`, then the safety rules are directly derived
    /// from the safety rules for [`<*const T>::offset_from`] method of `*const T`.
    ///
    /// Thus, in order to uphold the safety contracts for [`<*const T>::offset_from`]
    /// method, as well as for the correct logic of the work of this crate, the
    /// following rules are necessary and sufficient:
    ///
    /// * `base` contained pointer must not be `dangling` and must point to the
    ///   end of the first `element` from the `data part` of the table, i.e.
    ///   must be a pointer that returns by [`RawTable::data_end`] or by
    ///   [`RawTableInner::data_end<T>`];
    ///
    /// * `self` also must not contain dangling pointer;
    ///
    /// * both `self` and `base` must be created from the same [`RawTable`]
    ///   (or [`RawTableInner`]).
    ///
    /// If `mem::size_of::<T>() == 0`, this function is always safe.
    ///
    /// [`Bucket`]: crate::raw::Bucket
    /// [`from_base_index`]: crate::raw::Bucket::from_base_index
    /// [`RawTable::data_end`]: crate::raw::RawTable::data_end
    /// [`RawTableInner::data_end<T>`]: RawTableInner::data_end<T>
    /// [`RawTable`]: crate::raw::RawTable
    /// [`RawTableInner`]: RawTableInner
    /// [`<*const T>::offset_from`]: https://doc.rust-lang.org/nightly/core/primitive.pointer.html#method.offset_from
    #[inline]
    unsafe fn to_base_index(&self, base: NonNull<T>) -> usize {
        // If mem::size_of::<T>() != 0 then return an index under which we used to store the
        // `element` in the data part of the table (we start counting from "0", so
        // that in the expression T[last], the "last" index actually is one less than the
        // "buckets" number in the table, i.e. "last = RawTableInner.bucket_mask").
        // For example for 5th element in table calculation is performed like this:
        //
        //                        mem::size_of::<T>()
        //                          |
        //                          |         `self = from_base_index(base, 5)` that returns pointer
        //                          |         that points here in tha data part of the table
        //                          |         (to the end of T5)
        //                          |           |                    `base: NonNull<T>` must point here
        //                          v           |                    (to the end of T0 or to the start of C0)
        //                        /???\         v                      v
        // [Padding], Tlast, ..., |T10|, ..., T5|, T4, T3, T2, T1, T0, |C0, C1, C2, C3, C4, C5, ..., C10, ..., Clast
        //                                      \__________  __________/
        //                                                 \/
        //                                     `bucket.to_base_index(base)` = 5
        //                                     (base.as_ptr() as usize - self.ptr.as_ptr() as usize) / mem::size_of::<T>()
        //
        // where: T0...Tlast - our stored data; C0...Clast - control bytes or metadata for data.
        if Self::IS_ZERO_SIZED_TYPE {
            // this can not be UB
            self.ptr.as_ptr() as usize - 1
        } else {
            offset_from(base.as_ptr(), self.ptr.as_ptr())
        }
    }

    /// Acquires the underlying raw pointer `*mut T` to `data`.
    ///
    /// # Note
    ///
    /// If `T` is not [`Copy`], do not use `*mut T` methods that can cause calling the
    /// destructor of `T` (for example the [`<*mut T>::drop_in_place`] method), because
    /// for properly dropping the data we also need to clear `data` control bytes. If we
    /// drop data, but do not clear `data control byte` it leads to double drop when
    /// [`RawTable`] goes out of scope.
    ///
    /// If you modify an already initialized `value`, so [`Hash`] and [`Eq`] on the new
    /// `T` value and its borrowed form *must* match those for the old `T` value, as the map
    /// will not re-evaluate where the new value should go, meaning the value may become
    /// "lost" if their location does not reflect their state.
    ///
    /// [`RawTable`]: crate::raw::RawTable
    /// [`<*mut T>::drop_in_place`]: https://doc.rust-lang.org/core/primitive.pointer.html#method.drop_in_place
    /// [`Hash`]: https://doc.rust-lang.org/core/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/core/cmp/trait.Eq.html
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "raw")]
    /// # fn test() {
    /// use core::hash::{BuildHasher, Hash};
    /// use hashbrown::raw::{Bucket, RawTable};
    ///
    /// type NewHashBuilder = core::hash::BuildHasherDefault<ahash::AHasher>;
    ///
    /// fn make_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let hash_builder = NewHashBuilder::default();
    /// let mut table = RawTable::new();
    ///
    /// let value = ("a", 100);
    /// let hash = make_hash(&hash_builder, &value.0);
    ///
    /// table.insert(hash, value.clone(), |val| make_hash(&hash_builder, &val.0));
    ///
    /// let bucket: Bucket<(&str, i32)> = table.find(hash, |(k1, _)| k1 == &value.0).unwrap();
    ///
    /// assert_eq!(unsafe { &*bucket.as_ptr() }, &("a", 100));
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "raw")]
    /// #     test()
    /// # }
    /// ```
    #[inline]
    pub fn as_ptr(&self) -> *mut T {
        if Self::IS_ZERO_SIZED_TYPE {
            // Just return an arbitrary ZST pointer which is properly aligned
            // invalid pointer is good enough for ZST
            invalid_mut(mem::align_of::<T>())
        } else {
            unsafe { self.ptr.as_ptr().sub(1) }
        }
    }

    /// Create a new [`Bucket`] that is offset from the `self` by the given
    /// `offset`. The pointer calculation is performed by calculating the
    /// offset from `self` pointer (convenience for `self.ptr.as_ptr().sub(offset)`).
    /// This function is used for iterators.
    ///
    /// `offset` is in units of `T`; e.g., a `offset` of 3 represents a pointer
    /// offset of `3 * size_of::<T>()` bytes.
    ///
    /// # Safety
    ///
    /// If `mem::size_of::<T>() != 0`, then the safety rules are directly derived
    /// from the safety rules for [`<*mut T>::sub`] method of `*mut T` and safety
    /// rules of [`NonNull::new_unchecked`] function.
    ///
    /// Thus, in order to uphold the safety contracts for [`<*mut T>::sub`] method
    /// and [`NonNull::new_unchecked`] function, as well as for the correct
    /// logic of the work of this crate, the following rules are necessary and
    /// sufficient:
    ///
    /// * `self` contained pointer must not be `dangling`;
    ///
    /// * `self.to_base_index() + ofset` must not be greater than `RawTableInner.bucket_mask`,
    ///   i.e. `(self.to_base_index() + ofset) <= RawTableInner.bucket_mask` or, in other
    ///   words, `self.to_base_index() + ofset + 1` must be no greater than the number returned
    ///   by the function [`RawTable::buckets`] or [`RawTableInner::buckets`].
    ///
    /// If `mem::size_of::<T>() == 0`, then the only requirement is that the
    /// `self.to_base_index() + ofset` must not be greater than `RawTableInner.bucket_mask`,
    /// i.e. `(self.to_base_index() + ofset) <= RawTableInner.bucket_mask` or, in other words,
    /// `self.to_base_index() + ofset + 1` must be no greater than the number returned by the
    /// function [`RawTable::buckets`] or [`RawTableInner::buckets`].
    ///
    /// [`Bucket`]: crate::raw::Bucket
    /// [`<*mut T>::sub`]: https://doc.rust-lang.org/core/primitive.pointer.html#method.sub-1
    /// [`NonNull::new_unchecked`]: https://doc.rust-lang.org/stable/std/ptr/struct.NonNull.html#method.new_unchecked
    /// [`RawTable::buckets`]: crate::raw::RawTable::buckets
    /// [`RawTableInner::buckets`]: RawTableInner::buckets
    #[inline]
    unsafe fn next_n(&self, offset: usize) -> Self {
        let ptr = if Self::IS_ZERO_SIZED_TYPE {
            // invalid pointer is good enough for ZST
            invalid_mut(self.ptr.as_ptr() as usize + offset)
        } else {
            self.ptr.as_ptr().sub(offset)
        };
        Self {
            ptr: NonNull::new_unchecked(ptr),
        }
    }

    /// Executes the destructor (if any) of the pointed-to `data`.
    ///
    /// # Safety
    ///
    /// See [`ptr::drop_in_place`] for safety concerns.
    ///
    /// You should use [`RawTable::erase`] instead of this function,
    /// or be careful with calling this function directly, because for
    /// properly dropping the data we need also clear `data` control bytes.
    /// If we drop data, but do not erase `data control byte` it leads to
    /// double drop when [`RawTable`] goes out of scope.
    ///
    /// [`ptr::drop_in_place`]: https://doc.rust-lang.org/core/ptr/fn.drop_in_place.html
    /// [`RawTable`]: crate::raw::RawTable
    /// [`RawTable::erase`]: crate::raw::RawTable::erase
    #[cfg_attr(feature = "inline-more", inline)]
    pub(crate) unsafe fn drop(&self) {
        self.as_ptr().drop_in_place();
    }

    /// Reads the `value` from `self` without moving it. This leaves the
    /// memory in `self` unchanged.
    ///
    /// # Safety
    ///
    /// See [`ptr::read`] for safety concerns.
    ///
    /// You should use [`RawTable::remove`] instead of this function,
    /// or be careful with calling this function directly, because compiler
    /// calls its destructor when readed `value` goes out of scope. It
    /// can cause double dropping when [`RawTable`] goes out of scope,
    /// because of not erased `data control byte`.
    ///
    /// [`ptr::read`]: https://doc.rust-lang.org/core/ptr/fn.read.html
    /// [`RawTable`]: crate::raw::RawTable
    /// [`RawTable::remove`]: crate::raw::RawTable::remove
    #[inline]
    pub(crate) unsafe fn read(&self) -> T {
        self.as_ptr().read()
    }

    /// Overwrites a memory location with the given `value` without reading
    /// or dropping the old value (like [`ptr::write`] function).
    ///
    /// # Safety
    ///
    /// See [`ptr::write`] for safety concerns.
    ///
    /// # Note
    ///
    /// [`Hash`] and [`Eq`] on the new `T` value and its borrowed form *must* match
    /// those for the old `T` value, as the map will not re-evaluate where the new
    /// value should go, meaning the value may become "lost" if their location
    /// does not reflect their state.
    ///
    /// [`ptr::write`]: https://doc.rust-lang.org/core/ptr/fn.write.html
    /// [`Hash`]: https://doc.rust-lang.org/core/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/core/cmp/trait.Eq.html
    #[inline]
    pub(crate) unsafe fn write(&self, val: T) {
        self.as_ptr().write(val);
    }

    /// Returns a shared immutable reference to the `value`.
    ///
    /// # Safety
    ///
    /// See [`NonNull::as_ref`] for safety concerns.
    ///
    /// [`NonNull::as_ref`]: https://doc.rust-lang.org/core/ptr/struct.NonNull.html#method.as_ref
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "raw")]
    /// # fn test() {
    /// use core::hash::{BuildHasher, Hash};
    /// use hashbrown::raw::{Bucket, RawTable};
    ///
    /// type NewHashBuilder = core::hash::BuildHasherDefault<ahash::AHasher>;
    ///
    /// fn make_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let hash_builder = NewHashBuilder::default();
    /// let mut table = RawTable::new();
    ///
    /// let value: (&str, String) = ("A pony", "is a small horse".to_owned());
    /// let hash = make_hash(&hash_builder, &value.0);
    ///
    /// table.insert(hash, value.clone(), |val| make_hash(&hash_builder, &val.0));
    ///
    /// let bucket: Bucket<(&str, String)> = table.find(hash, |(k, _)| k == &value.0).unwrap();
    ///
    /// assert_eq!(
    ///     unsafe { bucket.as_ref() },
    ///     &("A pony", "is a small horse".to_owned())
    /// );
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "raw")]
    /// #     test()
    /// # }
    /// ```
    #[inline]
    pub unsafe fn as_ref<'a>(&self) -> &'a T {
        &*self.as_ptr()
    }

    /// Returns a unique mutable reference to the `value`.
    ///
    /// # Safety
    ///
    /// See [`NonNull::as_mut`] for safety concerns.
    ///
    /// # Note
    ///
    /// [`Hash`] and [`Eq`] on the new `T` value and its borrowed form *must* match
    /// those for the old `T` value, as the map will not re-evaluate where the new
    /// value should go, meaning the value may become "lost" if their location
    /// does not reflect their state.
    ///
    /// [`NonNull::as_mut`]: https://doc.rust-lang.org/core/ptr/struct.NonNull.html#method.as_mut
    /// [`Hash`]: https://doc.rust-lang.org/core/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/core/cmp/trait.Eq.html
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "raw")]
    /// # fn test() {
    /// use core::hash::{BuildHasher, Hash};
    /// use hashbrown::raw::{Bucket, RawTable};
    ///
    /// type NewHashBuilder = core::hash::BuildHasherDefault<ahash::AHasher>;
    ///
    /// fn make_hash<K: Hash + ?Sized, S: BuildHasher>(hash_builder: &S, key: &K) -> u64 {
    ///     use core::hash::Hasher;
    ///     let mut state = hash_builder.build_hasher();
    ///     key.hash(&mut state);
    ///     state.finish()
    /// }
    ///
    /// let hash_builder = NewHashBuilder::default();
    /// let mut table = RawTable::new();
    ///
    /// let value: (&str, String) = ("A pony", "is a small horse".to_owned());
    /// let hash = make_hash(&hash_builder, &value.0);
    ///
    /// table.insert(hash, value.clone(), |val| make_hash(&hash_builder, &val.0));
    ///
    /// let bucket: Bucket<(&str, String)> = table.find(hash, |(k, _)| k == &value.0).unwrap();
    ///
    /// unsafe {
    ///     bucket
    ///         .as_mut()
    ///         .1
    ///         .push_str(" less than 147 cm at the withers")
    /// };
    /// assert_eq!(
    ///     unsafe { bucket.as_ref() },
    ///     &(
    ///         "A pony",
    ///         "is a small horse less than 147 cm at the withers".to_owned()
    ///     )
    /// );
    /// # }
    /// # fn main() {
    /// #     #[cfg(feature = "raw")]
    /// #     test()
    /// # }
    /// ```
    #[inline]
    pub unsafe fn as_mut<'a>(&self) -> &'a mut T {
        &mut *self.as_ptr()
    }

    /// Copies `size_of<T>` bytes from `other` to `self`. The source
    /// and destination may *not* overlap.
    ///
    /// # Safety
    ///
    /// See [`ptr::copy_nonoverlapping`] for safety concerns.
    ///
    /// Like [`read`], `copy_nonoverlapping` creates a bitwise copy of `T`, regardless of
    /// whether `T` is [`Copy`]. If `T` is not [`Copy`], using *both* the values
    /// in the region beginning at `*self` and the region beginning at `*other` can
    /// [violate memory safety].
    ///
    /// # Note
    ///
    /// [`Hash`] and [`Eq`] on the new `T` value and its borrowed form *must* match
    /// those for the old `T` value, as the map will not re-evaluate where the new
    /// value should go, meaning the value may become "lost" if their location
    /// does not reflect their state.
    ///
    /// [`ptr::copy_nonoverlapping`]: https://doc.rust-lang.org/core/ptr/fn.copy_nonoverlapping.html
    /// [`read`]: https://doc.rust-lang.org/core/ptr/fn.read.html
    /// [violate memory safety]: https://doc.rust-lang.org/std/ptr/fn.read.html#ownership-of-the-returned-value
    /// [`Hash`]: https://doc.rust-lang.org/core/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/core/cmp/trait.Eq.html
    #[cfg(feature = "raw")]
    #[inline]
    pub unsafe fn copy_from_nonoverlapping(&self, other: &Self) {
        self.as_ptr().copy_from_nonoverlapping(other.as_ptr(), 1);
    }
}

/// A raw hash table with an unsafe API.
pub struct RawTable<T, A: Allocator + Clone = Global> {
    table: RawTableInner<A>,
    // Tell dropck that we own instances of T.
    marker: PhantomData<T>,
}

/// Non-generic part of `RawTable` which allows functions to be instantiated only once regardless
/// of how many different key-value types are used.
struct RawTableInner<A> {
    // Mask to get an index from a hash value. The value is one less than the
    // number of buckets in the table.
    bucket_mask: usize,

    // [Padding], T1, T2, ..., Tlast, C1, C2, ...
    //                                ^ points here
    ctrl: NonNull<u8>,

    // Number of elements that can be inserted before we need to grow the table
    growth_left: usize,

    // Number of elements in the table, only really used by len()
    items: usize,

    alloc: A,
}

impl<T> RawTable<T, Global> {
    /// Creates a new empty hash table without allocating any memory.
    ///
    /// In effect this returns a table with exactly 1 bucket. However we can
    /// leave the data pointer dangling since that bucket is never written to
    /// due to our load factor forcing us to always have at least 1 free bucket.
    #[inline]
    pub const fn new() -> Self {
        Self {
            table: RawTableInner::new_in(Global),
            marker: PhantomData,
        }
    }

    /// Attempts to allocate a new hash table with at least enough capacity
    /// for inserting the given number of elements without reallocating.
    #[cfg(feature = "raw")]
    pub fn try_with_capacity(capacity: usize) -> Result<Self, TryReserveError> {
        Self::try_with_capacity_in(capacity, Global)
    }

    /// Allocates a new hash table with at least enough capacity for inserting
    /// the given number of elements without reallocating.
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_in(capacity, Global)
    }
}

impl<T, A: Allocator + Clone> RawTable<T, A> {
    const TABLE_LAYOUT: TableLayout = TableLayout::new::<T>();
    const DATA_NEEDS_DROP: bool = mem::needs_drop::<T>();

    /// Creates a new empty hash table without allocating any memory, using the
    /// given allocator.
    ///
    /// In effect this returns a table with exactly 1 bucket. However we can
    /// leave the data pointer dangling since that bucket is never written to
    /// due to our load factor forcing us to always have at least 1 free bucket.
    #[inline]
    pub const fn new_in(alloc: A) -> Self {
        Self {
            table: RawTableInner::new_in(alloc),
            marker: PhantomData,
        }
    }

    /// Allocates a new hash table with the given number of buckets.
    ///
    /// The control bytes are left uninitialized.
    #[cfg_attr(feature = "inline-more", inline)]
    unsafe fn new_uninitialized(
        alloc: A,
        buckets: usize,
        fallibility: Fallibility,
    ) -> Result<Self, TryReserveError> {
        debug_assert!(buckets.is_power_of_two());

        Ok(Self {
            table: RawTableInner::new_uninitialized(
                alloc,
                Self::TABLE_LAYOUT,
                buckets,
                fallibility,
            )?,
            marker: PhantomData,
        })
    }

    /// Attempts to allocate a new hash table with at least enough capacity
    /// for inserting the given number of elements without reallocating.
    fn fallible_with_capacity(
        alloc: A,
        capacity: usize,
        fallibility: Fallibility,
    ) -> Result<Self, TryReserveError> {
        Ok(Self {
            table: RawTableInner::fallible_with_capacity(
                alloc,
                Self::TABLE_LAYOUT,
                capacity,
                fallibility,
            )?,
            marker: PhantomData,
        })
    }

    /// Attempts to allocate a new hash table using the given allocator, with at least enough
    /// capacity for inserting the given number of elements without reallocating.
    #[cfg(feature = "raw")]
    pub fn try_with_capacity_in(capacity: usize, alloc: A) -> Result<Self, TryReserveError> {
        Self::fallible_with_capacity(alloc, capacity, Fallibility::Fallible)
    }

    /// Allocates a new hash table using the given allocator, with at least enough capacity for
    /// inserting the given number of elements without reallocating.
    pub fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        // Avoid `Result::unwrap_or_else` because it bloats LLVM IR.
        match Self::fallible_with_capacity(alloc, capacity, Fallibility::Infallible) {
            Ok(capacity) => capacity,
            Err(_) => unsafe { hint::unreachable_unchecked() },
        }
    }

    /// Returns a reference to the underlying allocator.
    #[inline]
    pub fn allocator(&self) -> &A {
        &self.table.alloc
    }

    /// Deallocates the table without dropping any entries.
    #[cfg_attr(feature = "inline-more", inline)]
    unsafe fn free_buckets(&mut self) {
        self.table.free_buckets(Self::TABLE_LAYOUT);
    }

    /// Returns pointer to one past last element of data table.
    #[inline]
    pub unsafe fn data_end(&self) -> NonNull<T> {
        NonNull::new_unchecked(self.table.ctrl.as_ptr().cast())
    }

    /// Returns pointer to start of data table.
    #[inline]
    #[cfg(any(feature = "raw", feature = "nightly"))]
    pub unsafe fn data_start(&self) -> *mut T {
        self.data_end().as_ptr().wrapping_sub(self.buckets())
    }

    /// Return the information about memory allocated by the table.
    ///
    /// `RawTable` allocates single memory block to store both data and metadata.
    /// This function returns allocation size and alignment and the beginning of the area.
    /// These are the arguments which will be passed to `dealloc` when the table is dropped.
    ///
    /// This function might be useful for memory profiling.
    #[inline]
    #[cfg(feature = "raw")]
    pub fn allocation_info(&self) -> (NonNull<u8>, Layout) {
        self.table.allocation_info_or_zero(Self::TABLE_LAYOUT)
    }

    /// Returns the index of a bucket from a `Bucket`.
    #[inline]
    pub unsafe fn bucket_index(&self, bucket: &Bucket<T>) -> usize {
        bucket.to_base_index(self.data_end())
    }

    /// Returns a pointer to an element in the table.
    #[inline]
    pub unsafe fn bucket(&self, index: usize) -> Bucket<T> {
        debug_assert_ne!(self.table.bucket_mask, 0);
        debug_assert!(index < self.buckets());
        Bucket::from_base_index(self.data_end(), index)
    }

    /// Erases an element from the table without dropping it.
    #[cfg_attr(feature = "inline-more", inline)]
    unsafe fn erase_no_drop(&mut self, item: &Bucket<T>) {
        let index = self.bucket_index(item);
        self.table.erase(index);
    }

    /// Erases an element from the table, dropping it in place.
    #[cfg_attr(feature = "inline-more", inline)]
    #[allow(clippy::needless_pass_by_value)]
    pub unsafe fn erase(&mut self, item: Bucket<T>) {
        // Erase the element from the table first since drop might panic.
        self.erase_no_drop(&item);
        item.drop();
    }

    /// Finds and erases an element from the table, dropping it in place.
    /// Returns true if an element was found.
    #[cfg(feature = "raw")]
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn erase_entry(&mut self, hash: u64, eq: impl FnMut(&T) -> bool) -> bool {
        // Avoid `Option::map` because it bloats LLVM IR.
        if let Some(bucket) = self.find(hash, eq) {
            unsafe {
                self.erase(bucket);
            }
            true
        } else {
            false
        }
    }

    /// Removes an element from the table, returning it.
    #[cfg_attr(feature = "inline-more", inline)]
    #[allow(clippy::needless_pass_by_value)]
    pub unsafe fn remove(&mut self, item: Bucket<T>) -> T {
        self.erase_no_drop(&item);
        item.read()
    }

    /// Finds and removes an element from the table, returning it.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove_entry(&mut self, hash: u64, eq: impl FnMut(&T) -> bool) -> Option<T> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.find(hash, eq) {
            Some(bucket) => Some(unsafe { self.remove(bucket) }),
            None => None,
        }
    }

    /// Marks all table buckets as empty without dropping their contents.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn clear_no_drop(&mut self) {
        self.table.clear_no_drop();
    }

    /// Removes all elements from the table without freeing the backing memory.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn clear(&mut self) {
        // Ensure that the table is reset even if one of the drops panic
        let mut self_ = guard(self, |self_| self_.clear_no_drop());
        unsafe {
            self_.drop_elements();
        }
    }

    unsafe fn drop_elements(&mut self) {
        if Self::DATA_NEEDS_DROP && !self.is_empty() {
            for item in self.iter() {
                item.drop();
            }
        }
    }

    /// Shrinks the table to fit `max(self.len(), min_size)` elements.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn shrink_to(&mut self, min_size: usize, hasher: impl Fn(&T) -> u64) {
        // Calculate the minimal number of elements that we need to reserve
        // space for.
        let min_size = usize::max(self.table.items, min_size);
        if min_size == 0 {
            *self = Self::new_in(self.table.alloc.clone());
            return;
        }

        // Calculate the number of buckets that we need for this number of
        // elements. If the calculation overflows then the requested bucket
        // count must be larger than what we have right and nothing needs to be
        // done.
        let min_buckets = match capacity_to_buckets(min_size) {
            Some(buckets) => buckets,
            None => return,
        };

        // If we have more buckets than we need, shrink the table.
        if min_buckets < self.buckets() {
            // Fast path if the table is empty
            if self.table.items == 0 {
                *self = Self::with_capacity_in(min_size, self.table.alloc.clone());
            } else {
                // Avoid `Result::unwrap_or_else` because it bloats LLVM IR.
                if self
                    .resize(min_size, hasher, Fallibility::Infallible)
                    .is_err()
                {
                    unsafe { hint::unreachable_unchecked() }
                }
            }
        }
    }

    /// Ensures that at least `additional` items can be inserted into the table
    /// without reallocation.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn reserve(&mut self, additional: usize, hasher: impl Fn(&T) -> u64) {
        if unlikely(additional > self.table.growth_left) {
            // Avoid `Result::unwrap_or_else` because it bloats LLVM IR.
            if self
                .reserve_rehash(additional, hasher, Fallibility::Infallible)
                .is_err()
            {
                unsafe { hint::unreachable_unchecked() }
            }
        }
    }

    /// Tries to ensure that at least `additional` items can be inserted into
    /// the table without reallocation.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn try_reserve(
        &mut self,
        additional: usize,
        hasher: impl Fn(&T) -> u64,
    ) -> Result<(), TryReserveError> {
        if additional > self.table.growth_left {
            self.reserve_rehash(additional, hasher, Fallibility::Fallible)
        } else {
            Ok(())
        }
    }

    /// Out-of-line slow path for `reserve` and `try_reserve`.
    #[cold]
    #[inline(never)]
    fn reserve_rehash(
        &mut self,
        additional: usize,
        hasher: impl Fn(&T) -> u64,
        fallibility: Fallibility,
    ) -> Result<(), TryReserveError> {
        unsafe {
            self.table.reserve_rehash_inner(
                additional,
                &|table, index| hasher(table.bucket::<T>(index).as_ref()),
                fallibility,
                Self::TABLE_LAYOUT,
                if Self::DATA_NEEDS_DROP {
                    Some(mem::transmute(ptr::drop_in_place::<T> as unsafe fn(*mut T)))
                } else {
                    None
                },
            )
        }
    }

    /// Allocates a new table of a different size and moves the contents of the
    /// current table into it.
    fn resize(
        &mut self,
        capacity: usize,
        hasher: impl Fn(&T) -> u64,
        fallibility: Fallibility,
    ) -> Result<(), TryReserveError> {
        unsafe {
            self.table.resize_inner(
                capacity,
                &|table, index| hasher(table.bucket::<T>(index).as_ref()),
                fallibility,
                Self::TABLE_LAYOUT,
            )
        }
    }

    /// Inserts a new element into the table, and returns its raw bucket.
    ///
    /// This does not check if the given element already exists in the table.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert(&mut self, hash: u64, value: T, hasher: impl Fn(&T) -> u64) -> Bucket<T> {
        unsafe {
            let mut index = self.table.find_insert_slot(hash);

            // We can avoid growing the table once we have reached our load
            // factor if we are replacing a tombstone. This works since the
            // number of EMPTY slots does not change in this case.
            let old_ctrl = *self.table.ctrl(index);
            if unlikely(self.table.growth_left == 0 && special_is_empty(old_ctrl)) {
                self.reserve(1, hasher);
                index = self.table.find_insert_slot(hash);
            }

            self.table.record_item_insert_at(index, old_ctrl, hash);

            let bucket = self.bucket(index);
            bucket.write(value);
            bucket
        }
    }

    /// Attempts to insert a new element without growing the table and return its raw bucket.
    ///
    /// Returns an `Err` containing the given element if inserting it would require growing the
    /// table.
    ///
    /// This does not check if the given element already exists in the table.
    #[cfg(feature = "raw")]
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn try_insert_no_grow(&mut self, hash: u64, value: T) -> Result<Bucket<T>, T> {
        unsafe {
            match self.table.prepare_insert_no_grow(hash) {
                Ok(index) => {
                    let bucket = self.bucket(index);
                    bucket.write(value);
                    Ok(bucket)
                }
                Err(()) => Err(value),
            }
        }
    }

    /// Inserts a new element into the table, and returns a mutable reference to it.
    ///
    /// This does not check if the given element already exists in the table.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert_entry(&mut self, hash: u64, value: T, hasher: impl Fn(&T) -> u64) -> &mut T {
        unsafe { self.insert(hash, value, hasher).as_mut() }
    }

    /// Inserts a new element into the table, without growing the table.
    ///
    /// There must be enough space in the table to insert the new element.
    ///
    /// This does not check if the given element already exists in the table.
    #[cfg_attr(feature = "inline-more", inline)]
    #[cfg(any(feature = "raw", feature = "rustc-internal-api"))]
    pub unsafe fn insert_no_grow(&mut self, hash: u64, value: T) -> Bucket<T> {
        let (index, old_ctrl) = self.table.prepare_insert_slot(hash);
        let bucket = self.table.bucket(index);

        // If we are replacing a DELETED entry then we don't need to update
        // the load counter.
        self.table.growth_left -= special_is_empty(old_ctrl) as usize;

        bucket.write(value);
        self.table.items += 1;
        bucket
    }

    /// Temporary removes a bucket, applying the given function to the removed
    /// element and optionally put back the returned value in the same bucket.
    ///
    /// Returns `true` if the bucket still contains an element
    ///
    /// This does not check if the given bucket is actually occupied.
    #[cfg_attr(feature = "inline-more", inline)]
    pub unsafe fn replace_bucket_with<F, R>(&mut self, bucket: Bucket<T>, f: F) -> (bool, R)
    where
        F: FnOnce(T) -> (Option<T>, R),
    {
        let index = self.bucket_index(&bucket);
        let old_ctrl = *self.table.ctrl(index);
        debug_assert!(self.is_bucket_full(index));
        let old_growth_left = self.table.growth_left;
        let item = self.remove(bucket);
        match f(item) {
            (Some(new_item), r) => {
                self.table.growth_left = old_growth_left;
                self.table.set_ctrl(index, old_ctrl);
                self.table.items += 1;
                self.bucket(index).write(new_item);
                (true, r)
            }
            (None, r) => (false, r),
        }
    }

    /// Searches for an element in the table,
    /// or a potential slot where that element could be inserted.
    #[inline]
    pub fn find_potential(&self, hash: u64, mut eq: impl FnMut(&T) -> bool) -> (usize, bool) {
        self.table.find_potential_inner(hash, &mut |index| unsafe {
            eq(self.bucket(index).as_ref())
        })
    }

    /// Marks an element in the table as inserted.
    #[inline]
    pub unsafe fn mark_inserted(&mut self, index: usize, hash: u64) {
        let old_ctrl = *self.table.ctrl(index);
        self.table.record_item_insert_at(index, old_ctrl, hash);
    }

    /// Searches for an element in the table.
    #[inline]
    pub fn find(&self, hash: u64, mut eq: impl FnMut(&T) -> bool) -> Option<Bucket<T>> {
        let result = self.table.find_inner(hash, &mut |index| unsafe {
            eq(self.bucket(index).as_ref())
        });

        // Avoid `Option::map` because it bloats LLVM IR.
        match result {
            Some(index) => Some(unsafe { self.bucket(index) }),
            None => None,
        }
    }

    /// Gets a reference to an element in the table.
    #[inline]
    pub fn get(&self, hash: u64, eq: impl FnMut(&T) -> bool) -> Option<&T> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.find(hash, eq) {
            Some(bucket) => Some(unsafe { bucket.as_ref() }),
            None => None,
        }
    }

    /// Gets a mutable reference to an element in the table.
    #[inline]
    pub fn get_mut(&mut self, hash: u64, eq: impl FnMut(&T) -> bool) -> Option<&mut T> {
        // Avoid `Option::map` because it bloats LLVM IR.
        match self.find(hash, eq) {
            Some(bucket) => Some(unsafe { bucket.as_mut() }),
            None => None,
        }
    }

    /// Attempts to get mutable references to `N` entries in the table at once.
    ///
    /// Returns an array of length `N` with the results of each query.
    ///
    /// At most one mutable reference will be returned to any entry. `None` will be returned if any
    /// of the hashes are duplicates. `None` will be returned if the hash is not found.
    ///
    /// The `eq` argument should be a closure such that `eq(i, k)` returns true if `k` is equal to
    /// the `i`th key to be looked up.
    pub fn get_many_mut<const N: usize>(
        &mut self,
        hashes: [u64; N],
        eq: impl FnMut(usize, &T) -> bool,
    ) -> Option<[&'_ mut T; N]> {
        unsafe {
            let ptrs = self.get_many_mut_pointers(hashes, eq)?;

            for (i, &cur) in ptrs.iter().enumerate() {
                if ptrs[..i].iter().any(|&prev| ptr::eq::<T>(prev, cur)) {
                    return None;
                }
            }
            // All bucket are distinct from all previous buckets so we're clear to return the result
            // of the lookup.

            // TODO use `MaybeUninit::array_assume_init` here instead once that's stable.
            Some(mem::transmute_copy(&ptrs))
        }
    }

    pub unsafe fn get_many_unchecked_mut<const N: usize>(
        &mut self,
        hashes: [u64; N],
        eq: impl FnMut(usize, &T) -> bool,
    ) -> Option<[&'_ mut T; N]> {
        let ptrs = self.get_many_mut_pointers(hashes, eq)?;
        Some(mem::transmute_copy(&ptrs))
    }

    unsafe fn get_many_mut_pointers<const N: usize>(
        &mut self,
        hashes: [u64; N],
        mut eq: impl FnMut(usize, &T) -> bool,
    ) -> Option<[*mut T; N]> {
        // TODO use `MaybeUninit::uninit_array` here instead once that's stable.
        let mut outs: MaybeUninit<[*mut T; N]> = MaybeUninit::uninit();
        let outs_ptr = outs.as_mut_ptr();

        for (i, &hash) in hashes.iter().enumerate() {
            let cur = self.find(hash, |k| eq(i, k))?;
            *(*outs_ptr).get_unchecked_mut(i) = cur.as_mut();
        }

        // TODO use `MaybeUninit::array_assume_init` here instead once that's stable.
        Some(outs.assume_init())
    }

    /// Returns the number of elements the map can hold without reallocating.
    ///
    /// This number is a lower bound; the table might be able to hold
    /// more, but is guaranteed to be able to hold at least this many.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.table.items + self.table.growth_left
    }

    /// Returns the number of elements in the table.
    #[inline]
    pub fn len(&self) -> usize {
        self.table.items
    }

    /// Returns `true` if the table contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the number of buckets in the table.
    #[inline]
    pub fn buckets(&self) -> usize {
        self.table.bucket_mask + 1
    }

    /// Checks whether the bucket at `index` is full.
    ///
    /// # Safety
    ///
    /// The caller must ensure `index` is less than the number of buckets.
    #[inline]
    pub unsafe fn is_bucket_full(&self, index: usize) -> bool {
        self.table.is_bucket_full(index)
    }

    /// Returns an iterator over every element in the table. It is up to
    /// the caller to ensure that the `RawTable` outlives the `RawIter`.
    /// Because we cannot make the `next` method unsafe on the `RawIter`
    /// struct, we have to make the `iter` method unsafe.
    #[inline]
    pub unsafe fn iter(&self) -> RawIter<T> {
        let data = Bucket::from_base_index(self.data_end(), 0);
        RawIter {
            iter: RawIterRange::new(self.table.ctrl.as_ptr(), data, self.table.buckets()),
            items: self.table.items,
        }
    }

    /// Returns an iterator over occupied buckets that could match a given hash.
    ///
    /// `RawTable` only stores 7 bits of the hash value, so this iterator may
    /// return items that have a hash value different than the one provided. You
    /// should always validate the returned values before using them.
    ///
    /// It is up to the caller to ensure that the `RawTable` outlives the
    /// `RawIterHash`. Because we cannot make the `next` method unsafe on the
    /// `RawIterHash` struct, we have to make the `iter_hash` method unsafe.
    #[cfg_attr(feature = "inline-more", inline)]
    #[cfg(feature = "raw")]
    pub unsafe fn iter_hash(&self, hash: u64) -> RawIterHash<'_, T, A> {
        RawIterHash::new(self, hash)
    }

    /// Returns an iterator which removes all elements from the table without
    /// freeing the memory.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn drain(&mut self) -> RawDrain<'_, T, A> {
        unsafe {
            let iter = self.iter();
            self.drain_iter_from(iter)
        }
    }

    /// Returns an iterator which removes all elements from the table without
    /// freeing the memory.
    ///
    /// Iteration starts at the provided iterator's current location.
    ///
    /// It is up to the caller to ensure that the iterator is valid for this
    /// `RawTable` and covers all items that remain in the table.
    #[cfg_attr(feature = "inline-more", inline)]
    pub unsafe fn drain_iter_from(&mut self, iter: RawIter<T>) -> RawDrain<'_, T, A> {
        debug_assert_eq!(iter.len(), self.len());
        RawDrain {
            iter,
            table: ManuallyDrop::new(mem::replace(self, Self::new_in(self.table.alloc.clone()))),
            orig_table: NonNull::from(self),
            marker: PhantomData,
        }
    }

    /// Returns an iterator which consumes all elements from the table.
    ///
    /// Iteration starts at the provided iterator's current location.
    ///
    /// It is up to the caller to ensure that the iterator is valid for this
    /// `RawTable` and covers all items that remain in the table.
    pub unsafe fn into_iter_from(self, iter: RawIter<T>) -> RawIntoIter<T, A> {
        debug_assert_eq!(iter.len(), self.len());

        let alloc = self.table.alloc.clone();
        let allocation = self.into_allocation();
        RawIntoIter {
            iter,
            allocation,
            marker: PhantomData,
            alloc,
        }
    }

    /// Converts the table into a raw allocation. The contents of the table
    /// should be dropped using a `RawIter` before freeing the allocation.
    #[cfg_attr(feature = "inline-more", inline)]
    pub(crate) fn into_allocation(self) -> Option<(NonNull<u8>, Layout)> {
        let alloc = if self.table.is_empty_singleton() {
            None
        } else {
            // Avoid `Option::unwrap_or_else` because it bloats LLVM IR.
            let (layout, ctrl_offset) =
                match Self::TABLE_LAYOUT.calculate_layout_for(self.table.buckets()) {
                    Some(lco) => lco,
                    None => unsafe { hint::unreachable_unchecked() },
                };
            Some((
                unsafe { NonNull::new_unchecked(self.table.ctrl.as_ptr().sub(ctrl_offset)) },
                layout,
            ))
        };
        mem::forget(self);
        alloc
    }
}

unsafe impl<T, A: Allocator + Clone> Send for RawTable<T, A>
where
    T: Send,
    A: Send,
{
}
unsafe impl<T, A: Allocator + Clone> Sync for RawTable<T, A>
where
    T: Sync,
    A: Sync,
{
}

impl<A> RawTableInner<A> {
    /// Creates a new empty hash table without allocating any memory.
    ///
    /// In effect this returns a table with exactly 1 bucket. However we can
    /// leave the data pointer dangling since that bucket is never accessed
    /// due to our load factor forcing us to always have at least 1 free bucket.
    #[inline]
    const fn new_in(alloc: A) -> Self {
        Self {
            // Be careful to cast the entire slice to a raw pointer.
            ctrl: unsafe { NonNull::new_unchecked(Group::static_empty() as *const _ as *mut u8) },
            bucket_mask: 0,
            items: 0,
            growth_left: 0,
            alloc,
        }
    }
}

impl<A: Allocator + Clone> RawTableInner<A> {
    /// Allocates a new [`RawTableInner`] with the given number of buckets.
    /// The control bytes and buckets are left uninitialized.
    ///
    /// # Safety
    ///
    /// The caller of this function must ensure that the `buckets` is power of two
    /// and also initialize all control bytes of the length `self.bucket_mask + 1 +
    /// Group::WIDTH` with the [`EMPTY`] bytes.
    ///
    /// See also [`Allocator`] API for other safety concerns.
    ///
    /// [`Allocator`]: https://doc.rust-lang.org/alloc/alloc/trait.Allocator.html
    #[cfg_attr(feature = "inline-more", inline)]
    unsafe fn new_uninitialized(
        alloc: A,
        table_layout: TableLayout,
        buckets: usize,
        fallibility: Fallibility,
    ) -> Result<Self, TryReserveError> {
        debug_assert!(buckets.is_power_of_two());

        // Avoid `Option::ok_or_else` because it bloats LLVM IR.
        let (layout, ctrl_offset) = match table_layout.calculate_layout_for(buckets) {
            Some(lco) => lco,
            None => return Err(fallibility.capacity_overflow()),
        };

        let ptr: NonNull<u8> = match do_alloc(&alloc, layout) {
            Ok(block) => block.cast(),
            Err(_) => return Err(fallibility.alloc_err(layout)),
        };

        // SAFETY: null pointer will be caught in above check
        let ctrl = NonNull::new_unchecked(ptr.as_ptr().add(ctrl_offset));
        Ok(Self {
            ctrl,
            bucket_mask: buckets - 1,
            items: 0,
            growth_left: bucket_mask_to_capacity(buckets - 1),
            alloc,
        })
    }

    /// Attempts to allocate a new [`RawTableInner`] with at least enough
    /// capacity for inserting the given number of elements without reallocating.
    ///
    /// All the control bytes are initialized with the [`EMPTY`] bytes.
    #[inline]
    fn fallible_with_capacity(
        alloc: A,
        table_layout: TableLayout,
        capacity: usize,
        fallibility: Fallibility,
    ) -> Result<Self, TryReserveError> {
        if capacity == 0 {
            Ok(Self::new_in(alloc))
        } else {
            // SAFETY: We checked that we could successfully allocate the new table, and then
            // initialized all control bytes with the constant `EMPTY` byte.
            unsafe {
                let buckets =
                    capacity_to_buckets(capacity).ok_or_else(|| fallibility.capacity_overflow())?;

                let result = Self::new_uninitialized(alloc, table_layout, buckets, fallibility)?;
                // SAFETY: We checked that the table is allocated and therefore the table already has
                // `self.bucket_mask + 1 + Group::WIDTH` number of control bytes (see TableLayout::calculate_layout_for)
                // so writing `self.num_ctrl_bytes() == bucket_mask + 1 + Group::WIDTH` bytes is safe.
                result.ctrl(0).write_bytes(EMPTY, result.num_ctrl_bytes());

                Ok(result)
            }
        }
    }

    /// Fixes up an insertion slot due to false positives for groups smaller than the group width.
    /// This must only be used on insertion slots found by `find_insert_slot_in_group`.
    #[inline]
    unsafe fn fix_insert_slot(&self, index: usize) -> usize {
        // In tables smaller than the group width
        // (self.buckets() < Group::WIDTH), trailing control
        // bytes outside the range of the table are filled with
        // EMPTY entries. These will unfortunately trigger a
        // match, but once masked may point to a full bucket that
        // is already occupied. We detect this situation here and
        // perform a second scan starting at the beginning of the
        // table. This second scan is guaranteed to find an empty
        // slot (due to the load factor) before hitting the trailing
        // control bytes (containing EMPTY).
        if unlikely(self.is_bucket_full(index)) {
            debug_assert!(self.bucket_mask < Group::WIDTH);
            // SAFETY:
            //
            // * We are in range and `ptr = self.ctrl(0)` are valid for reads
            //   and properly aligned, because the table is already allocated
            //   (see `TableLayout::calculate_layout_for` and `ptr::read`);
            //
            // * For tables larger than the group width (self.buckets() >= Group::WIDTH),
            //   we will never end up in the given branch, since
            //   `(probe_seq.pos + bit) & self.bucket_mask` in `find_insert_slot_in_group` cannot
            //   return a full bucket index. For tables smaller than the group width, calling the
            //   `lowest_set_bit_nonzero` function (when `nightly` feature enabled) is also
            //   safe, as the trailing control bytes outside the range of the table are filled
            //   with EMPTY bytes, so this second scan either finds an empty slot (due to the
            //   load factor) or hits the trailing control bytes (containing EMPTY). See
            //   `intrinsics::cttz_nonzero` for more information.
            Group::load_aligned(self.ctrl(0))
                .match_empty_or_deleted()
                .lowest_set_bit_nonzero()
        } else {
            index
        }
    }

    /// Finds the position to insert something in a group.
    /// This may have false positives and must be fixed up with `fix_insert_slot` before it's used.
    #[inline]
    fn find_insert_slot_in_group(&self, group: &Group, probe_seq: &ProbeSeq) -> Option<usize> {
        let bit = group.match_empty_or_deleted().lowest_set_bit();

        if likely(bit.is_some()) {
            Some((probe_seq.pos + bit.unwrap()) & self.bucket_mask)
        } else {
            None
        }
    }

    /// Searches for an element in the table, or a potential slot where that element could be
    /// inserted.
    ///
    /// This uses dynamic dispatch to reduce the amount of code generated, but that is
    /// eliminated by LLVM optimizations.
    #[inline]
    pub fn find_potential_inner(
        &self,
        hash: u64,
        eq: &mut dyn FnMut(usize) -> bool,
    ) -> (usize, bool) {
        let mut insert_slot = None;

        let h2_hash = h2(hash);
        let mut probe_seq = self.probe_seq(hash);

        loop {
            let group = unsafe { Group::load(self.ctrl(probe_seq.pos)) };

            for bit in group.match_byte(h2_hash) {
                let index = (probe_seq.pos + bit) & self.bucket_mask;

                if likely(eq(index)) {
                    return (index, true);
                }
            }

            // We didn't find the element we were looking for in the group, try to get an
            // insertion slot from the group if we don't have one yet.
            if likely(insert_slot.is_none()) {
                insert_slot = self.find_insert_slot_in_group(&group, &probe_seq);
            }

            // Only stop the search if the group contains at least one empty element.
            // Otherwise, the element that we are looking for might be in a following group.
            if likely(group.match_empty().any_bit_set()) {
                // We must have found a insert slot by now, since the current group contains at
                // least one. For tables smaller than the group width, there will still be an
                // empty element in the current (and only) group due to the load factor.
                unsafe {
                    return (self.fix_insert_slot(insert_slot.unwrap_unchecked()), false);
                }
            }

            probe_seq.move_next(self.bucket_mask);
        }
    }

    /// Searches for an empty or deleted bucket which is suitable for inserting
    /// a new element and sets the hash for that slot.
    ///
    /// There must be at least 1 empty bucket in the table.
    #[inline]
    unsafe fn prepare_insert_slot(&self, hash: u64) -> (usize, u8) {
        let index = self.find_insert_slot(hash);
        let old_ctrl = *self.ctrl(index);
        self.set_ctrl_h2(index, hash);
        (index, old_ctrl)
    }

    /// Searches for an empty or deleted bucket which is suitable for inserting
    /// a new element, returning the `index` for the new [`Bucket`].
    ///
    /// This function does not make any changes to the `data` part of the table, or any
    /// changes to the `items` or `growth_left` field of the table.
    ///
    /// The table must have at least 1 empty or deleted `bucket`, otherwise this function
    /// will never return (will go into an infinite loop) for tables larger than the group
    /// width, or return an index outside of the table indices range if the table is less
    /// than the group width.
    ///
    /// # Note
    ///
    /// Calling this function is always safe, but attempting to write data at
    /// the index returned by this function when the table is less than the group width
    /// and if there was not at least one empty bucket in the table will cause immediate
    /// [`undefined behavior`]. This is because in this case the function will return
    /// `self.bucket_mask + 1` as an index due to the trailing EMPTY control bytes outside
    /// the table range.
    ///
    /// [`undefined behavior`]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    fn find_insert_slot(&self, hash: u64) -> usize {
        let mut probe_seq = self.probe_seq(hash);
        loop {
            // SAFETY:
            // * `ProbeSeq.pos` cannot be greater than `self.bucket_mask = self.buckets() - 1`
            //   of the table due to masking with `self.bucket_mask` and also because mumber of
            //   buckets is a power of two (see comment for masking below).
            //
            // * Even if `ProbeSeq.pos` returns `position == self.bucket_mask`, it is safe to
            //   call `Group::load` due to the extended control bytes range, which is
            //  `self.bucket_mask + 1 + Group::WIDTH` (in fact, this means that the last control
            //   byte will never be read for the allocated table);
            //
            // * Also, even if `RawTableInner` is not already allocated, `ProbeSeq.pos` will
            //   always return "0" (zero), so Group::load will read unaligned `Group::static_empty()`
            //   bytes, which is safe (see RawTableInner::new_in).
            unsafe {
                let group = Group::load(self.ctrl(probe_seq.pos));
                let index = self.find_insert_slot_in_group(&group, &probe_seq);

                if likely(index.is_some()) {
                    return self.fix_insert_slot(index.unwrap_unchecked());
                }
            }
            probe_seq.move_next(self.bucket_mask);
        }
    }

    /// Searches for an element in a table, returning the `index` of the found element.
    /// This uses dynamic dispatch to reduce the amount of code generated, but it is
    /// eliminated by LLVM optimizations.
    ///
    /// This function does not make any changes to the `data` part of the table, or any
    /// changes to the `items` or `growth_left` field of the table.
    ///
    /// The table must have at least 1 empty `bucket`, otherwise, if the
    /// `eq: &mut dyn FnMut(usize) -> bool` function does not return `true`,
    /// this function will also never return (will go into an infinite loop).
    #[inline(always)]
    fn find_inner(&self, hash: u64, eq: &mut dyn FnMut(usize) -> bool) -> Option<usize> {
        let h2_hash = h2(hash);
        let mut probe_seq = self.probe_seq(hash);

        loop {
            // SAFETY:
            // * `ProbeSeq.pos` cannot be greater than `self.bucket_mask = self.buckets() - 1`
            //   of the table due to masking with `self.bucket_mask`.
            //
            // * Even if `ProbeSeq.pos` returns `position == self.bucket_mask`, it is safe to
            //   call `Group::load` due to the extended control bytes range, which is
            //  `self.bucket_mask + 1 + Group::WIDTH` (in fact, this means that the last control
            //   byte will never be read for the allocated table);
            //
            // * Also, even if `RawTableInner` is not already allocated, `ProbeSeq.pos` will
            //   always return "0" (zero), so Group::load will read unaligned `Group::static_empty()`
            //   bytes, which is safe (see RawTableInner::new_in).
            let group = unsafe { Group::load(self.ctrl(probe_seq.pos)) };

            for bit in group.match_byte(h2_hash) {
                // This is the same as `(probe_seq.pos + bit) % self.buckets()` because the number
                // of buckets is a power of two, and `self.bucket_mask = self.buckets() - 1`.
                let index = (probe_seq.pos + bit) & self.bucket_mask;

                if likely(eq(index)) {
                    return Some(index);
                }
            }

            if likely(group.match_empty().any_bit_set()) {
                return None;
            }

            probe_seq.move_next(self.bucket_mask);
        }
    }

    /// Prepares for rehashing data in place (that is, without allocating new memory).
    /// Converts all full index `control bytes` to `DELETED` and all `DELETED` control
    /// bytes to `EMPTY`, i.e. performs the following conversion:
    ///
    /// - `EMPTY` control bytes   -> `EMPTY`;
    /// - `DELETED` control bytes -> `EMPTY`;
    /// - `FULL` control bytes    -> `DELETED`.
    ///
    /// This function does not make any changes to the `data` parts of the table,
    /// or any changes to the the `items` or `growth_left` field of the table.
    ///
    /// # Safety
    ///
    /// You must observe the following safety rules when calling this function:
    ///
    /// * The [`RawTableInner`] has already been allocated;
    ///
    /// * The caller of this function must convert the `DELETED` bytes back to `FULL`
    ///   bytes when re-inserting them into their ideal position (which was impossible
    ///   to do during the first insert due to tombstones). If the caller does not do
    ///   this, then calling this function may result in a memory leak.
    ///
    /// Calling this function on a table that has not been allocated results in
    /// [`undefined behavior`].
    ///
    /// See also [`Bucket::as_ptr`] method, for more information about of properly removing
    /// or saving `data element` from / into the [`RawTable`] / [`RawTableInner`].
    ///
    /// [`Bucket::as_ptr`]: Bucket::as_ptr
    /// [`undefined behavior`]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[allow(clippy::mut_mut)]
    #[inline]
    unsafe fn prepare_rehash_in_place(&mut self) {
        // Bulk convert all full control bytes to DELETED, and all DELETED control bytes to EMPTY.
        // This effectively frees up all buckets containing a DELETED entry.
        //
        // SAFETY:
        // 1. `i` is guaranteed to be within bounds since we are iterating from zero to `buckets - 1`;
        // 2. Even if `i` will be `i == self.bucket_mask`, it is safe to call `Group::load_aligned`
        //    due to the extended control bytes range, which is `self.bucket_mask + 1 + Group::WIDTH`;
        // 3. The caller of this function guarantees that [`RawTableInner`] has already been allocated;
        // 4. We can use `Group::load_aligned` and `Group::store_aligned` here since we start from 0
        //    and go to the end with a step equal to `Group::WIDTH` (see TableLayout::calculate_layout_for).
        for i in (0..self.buckets()).step_by(Group::WIDTH) {
            let group = Group::load_aligned(self.ctrl(i));
            let group = group.convert_special_to_empty_and_full_to_deleted();
            group.store_aligned(self.ctrl(i));
        }

        // Fix up the trailing control bytes. See the comments in set_ctrl
        // for the handling of tables smaller than the group width.
        //
        // SAFETY: The caller of this function guarantees that [`RawTableInner`]
        // has already been allocated
        if unlikely(self.buckets() < Group::WIDTH) {
            // SAFETY: We have `self.bucket_mask + 1 + Group::WIDTH` number of control bytes,
            // so copying `self.buckets() == self.bucket_mask + 1` bytes with offset equal to
            // `Group::WIDTH` is safe
            self.ctrl(0)
                .copy_to(self.ctrl(Group::WIDTH), self.buckets());
        } else {
            // SAFETY: We have `self.bucket_mask + 1 + Group::WIDTH` number of
            // control bytes,so copying `Group::WIDTH` bytes with offset equal
            // to `self.buckets() == self.bucket_mask + 1` is safe
            self.ctrl(0)
                .copy_to(self.ctrl(self.buckets()), Group::WIDTH);
        }
    }

    #[inline]
    unsafe fn bucket<T>(&self, index: usize) -> Bucket<T> {
        debug_assert_ne!(self.bucket_mask, 0);
        debug_assert!(index < self.buckets());
        Bucket::from_base_index(self.data_end(), index)
    }

    #[inline]
    unsafe fn bucket_ptr(&self, index: usize, size_of: usize) -> *mut u8 {
        debug_assert_ne!(self.bucket_mask, 0);
        debug_assert!(index < self.buckets());
        let base: *mut u8 = self.data_end().as_ptr();
        base.sub((index + 1) * size_of)
    }

    #[inline]
    unsafe fn data_end<T>(&self) -> NonNull<T> {
        NonNull::new_unchecked(self.ctrl.as_ptr().cast())
    }

    /// Returns an iterator-like object for a probe sequence on the table.
    ///
    /// This iterator never terminates, but is guaranteed to visit each bucket
    /// group exactly once. The loop using `probe_seq` must terminate upon
    /// reaching a group containing an empty bucket.
    #[inline]
    fn probe_seq(&self, hash: u64) -> ProbeSeq {
        ProbeSeq {
            pos: h1(hash) & self.bucket_mask,
            stride: 0,
        }
    }

    /// Returns the index of a bucket for which a value must be inserted if there is enough rooom
    /// in the table, otherwise returns error
    #[cfg(feature = "raw")]
    #[inline]
    unsafe fn prepare_insert_no_grow(&mut self, hash: u64) -> Result<usize, ()> {
        let index = self.find_insert_slot(hash);
        let old_ctrl = *self.ctrl(index);
        if unlikely(self.growth_left == 0 && special_is_empty(old_ctrl)) {
            Err(())
        } else {
            self.record_item_insert_at(index, old_ctrl, hash);
            Ok(index)
        }
    }

    #[inline]
    unsafe fn record_item_insert_at(&mut self, index: usize, old_ctrl: u8, hash: u64) {
        self.growth_left -= usize::from(special_is_empty(old_ctrl));
        self.set_ctrl_h2(index, hash);
        self.items += 1;
    }

    #[inline]
    fn is_in_same_group(&self, i: usize, new_i: usize, hash: u64) -> bool {
        let probe_seq_pos = self.probe_seq(hash).pos;
        let probe_index =
            |pos: usize| (pos.wrapping_sub(probe_seq_pos) & self.bucket_mask) / Group::WIDTH;
        probe_index(i) == probe_index(new_i)
    }

    /// Sets a control byte to the hash, and possibly also the replicated control byte at
    /// the end of the array.
    ///
    /// This function does not make any changes to the `data` parts of the table,
    /// or any changes to the the `items` or `growth_left` field of the table.
    ///
    /// # Safety
    ///
    /// The safety rules are directly derived from the safety rules for [`RawTableInner::set_ctrl`]
    /// method. Thus, in order to uphold the safety contracts for the method, you must observe the
    /// following rules when calling this function:
    ///
    /// * The [`RawTableInner`] has already been allocated;
    ///
    /// * The `index` must not be greater than the `RawTableInner.bucket_mask`, i.e.
    ///   `index <= RawTableInner.bucket_mask` or, in other words, `(index + 1)` must
    ///   be no greater than the number returned by the function [`RawTableInner::buckets`].
    ///
    /// Calling this function on a table that has not been allocated results in [`undefined behavior`].
    ///
    /// See also [`Bucket::as_ptr`] method, for more information about of properly removing
    /// or saving `data element` from / into the [`RawTable`] / [`RawTableInner`].
    ///
    /// [`RawTableInner::set_ctrl`]: RawTableInner::set_ctrl
    /// [`RawTableInner::buckets`]: RawTableInner::buckets
    /// [`Bucket::as_ptr`]: Bucket::as_ptr
    /// [`undefined behavior`]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    unsafe fn set_ctrl_h2(&self, index: usize, hash: u64) {
        // SAFETY: The caller must uphold the safety rules for the [`RawTableInner::set_ctrl_h2`]
        self.set_ctrl(index, h2(hash));
    }

    /// Replaces the hash in the control byte at the given index with the provided one,
    /// and possibly also replicates the new control byte at the end of the array of control
    /// bytes, returning the old control byte.
    ///
    /// This function does not make any changes to the `data` parts of the table,
    /// or any changes to the the `items` or `growth_left` field of the table.
    ///
    /// # Safety
    ///
    /// The safety rules are directly derived from the safety rules for [`RawTableInner::set_ctrl_h2`]
    /// and [`RawTableInner::ctrl`] methods. Thus, in order to uphold the safety contracts for both
    /// methods, you must observe the following rules when calling this function:
    ///
    /// * The [`RawTableInner`] has already been allocated;
    ///
    /// * The `index` must not be greater than the `RawTableInner.bucket_mask`, i.e.
    ///   `index <= RawTableInner.bucket_mask` or, in other words, `(index + 1)` must
    ///   be no greater than the number returned by the function [`RawTableInner::buckets`].
    ///
    /// Calling this function on a table that has not been allocated results in [`undefined behavior`].
    ///
    /// See also [`Bucket::as_ptr`] method, for more information about of properly removing
    /// or saving `data element` from / into the [`RawTable`] / [`RawTableInner`].
    ///
    /// [`RawTableInner::set_ctrl_h2`]: RawTableInner::set_ctrl_h2
    /// [`RawTableInner::buckets`]: RawTableInner::buckets
    /// [`Bucket::as_ptr`]: Bucket::as_ptr
    /// [`undefined behavior`]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    unsafe fn replace_ctrl_h2(&self, index: usize, hash: u64) -> u8 {
        // SAFETY: The caller must uphold the safety rules for the [`RawTableInner::replace_ctrl_h2`]
        let prev_ctrl = *self.ctrl(index);
        self.set_ctrl_h2(index, hash);
        prev_ctrl
    }

    /// Sets a control byte, and possibly also the replicated control byte at
    /// the end of the array.
    ///
    /// This function does not make any changes to the `data` parts of the table,
    /// or any changes to the the `items` or `growth_left` field of the table.
    ///
    /// # Safety
    ///
    /// You must observe the following safety rules when calling this function:
    ///
    /// * The [`RawTableInner`] has already been allocated;
    ///
    /// * The `index` must not be greater than the `RawTableInner.bucket_mask`, i.e.
    ///   `index <= RawTableInner.bucket_mask` or, in other words, `(index + 1)` must
    ///   be no greater than the number returned by the function [`RawTableInner::buckets`].
    ///
    /// Calling this function on a table that has not been allocated results in [`undefined behavior`].
    ///
    /// See also [`Bucket::as_ptr`] method, for more information about of properly removing
    /// or saving `data element` from / into the [`RawTable`] / [`RawTableInner`].
    ///
    /// [`RawTableInner::buckets`]: RawTableInner::buckets
    /// [`Bucket::as_ptr`]: Bucket::as_ptr
    /// [`undefined behavior`]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    unsafe fn set_ctrl(&self, index: usize, ctrl: u8) {
        // Replicate the first Group::WIDTH control bytes at the end of
        // the array without using a branch:
        // - If index >= Group::WIDTH then index == index2.
        // - Otherwise index2 == self.bucket_mask + 1 + index.
        //
        // The very last replicated control byte is never actually read because
        // we mask the initial index for unaligned loads, but we write it
        // anyways because it makes the set_ctrl implementation simpler.
        //
        // If there are fewer buckets than Group::WIDTH then this code will
        // replicate the buckets at the end of the trailing group. For example
        // with 2 buckets and a group size of 4, the control bytes will look
        // like this:
        //
        //     Real    |             Replicated
        // ---------------------------------------------
        // | [A] | [B] | [EMPTY] | [EMPTY] | [A] | [B] |
        // ---------------------------------------------

        // This is the same as `(index.wrapping_sub(Group::WIDTH)) % self.buckets() + Group::WIDTH`
        // because the number of buckets is a power of two, and `self.bucket_mask = self.buckets() - 1`.
        let index2 = ((index.wrapping_sub(Group::WIDTH)) & self.bucket_mask) + Group::WIDTH;

        // SAFETY: The caller must uphold the safety rules for the [`RawTableInner::set_ctrl`]
        *self.ctrl(index) = ctrl;
        *self.ctrl(index2) = ctrl;
    }

    /// Returns a pointer to a control byte.
    ///
    /// # Safety
    ///
    /// For the allocated [`RawTableInner`], the result is [`Undefined Behavior`],
    /// if the `index` is greater than the `self.bucket_mask + 1 + Group::WIDTH`.
    /// In that case, calling this function with `index == self.bucket_mask + 1 + Group::WIDTH`
    /// will return a pointer to the end of the allocated table and it is useless on its own.
    ///
    /// Calling this function with `index >= self.bucket_mask + 1 + Group::WIDTH` on a
    /// table that has not been allocated results in [`Undefined Behavior`].
    ///
    /// So to satisfy both requirements you should always follow the rule that
    /// `index < self.bucket_mask + 1 + Group::WIDTH`
    ///
    /// Calling this function on [`RawTableInner`] that are not already allocated is safe
    /// for read-only purpose.
    ///
    /// See also [`Bucket::as_ptr()`] method, for more information about of properly removing
    /// or saving `data element` from / into the [`RawTable`] / [`RawTableInner`].
    ///
    /// [`Bucket::as_ptr()`]: Bucket::as_ptr()
    /// [`Undefined Behavior`]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    unsafe fn ctrl(&self, index: usize) -> *mut u8 {
        debug_assert!(index < self.num_ctrl_bytes());
        // SAFETY: The caller must uphold the safety rules for the [`RawTableInner::ctrl`]
        self.ctrl.as_ptr().add(index)
    }

    #[inline]
    fn buckets(&self) -> usize {
        self.bucket_mask + 1
    }

    /// Checks whether the bucket at `index` is full.
    ///
    /// # Safety
    ///
    /// The caller must ensure `index` is less than the number of buckets.
    #[inline]
    unsafe fn is_bucket_full(&self, index: usize) -> bool {
        debug_assert!(index < self.buckets());
        is_full(*self.ctrl(index))
    }

    #[inline]
    fn num_ctrl_bytes(&self) -> usize {
        self.bucket_mask + 1 + Group::WIDTH
    }

    #[inline]
    fn is_empty_singleton(&self) -> bool {
        self.bucket_mask == 0
    }

    #[allow(clippy::mut_mut)]
    #[inline]
    unsafe fn prepare_resize(
        &self,
        table_layout: TableLayout,
        capacity: usize,
        fallibility: Fallibility,
    ) -> Result<crate::scopeguard::ScopeGuard<Self, impl FnMut(&mut Self)>, TryReserveError> {
        debug_assert!(self.items <= capacity);

        // Allocate and initialize the new table.
        let mut new_table = RawTableInner::fallible_with_capacity(
            self.alloc.clone(),
            table_layout,
            capacity,
            fallibility,
        )?;
        new_table.growth_left -= self.items;
        new_table.items = self.items;

        // The hash function may panic, in which case we simply free the new
        // table without dropping any elements that may have been copied into
        // it.
        //
        // This guard is also used to free the old table on success, see
        // the comment at the bottom of this function.
        Ok(guard(new_table, move |self_| {
            if !self_.is_empty_singleton() {
                self_.free_buckets(table_layout);
            }
        }))
    }

    /// Reserves or rehashes to make room for `additional` more elements.
    ///
    /// This uses dynamic dispatch to reduce the amount of
    /// code generated, but it is eliminated by LLVM optimizations when inlined.
    #[allow(clippy::inline_always)]
    #[inline(always)]
    unsafe fn reserve_rehash_inner(
        &mut self,
        additional: usize,
        hasher: &dyn Fn(&mut Self, usize) -> u64,
        fallibility: Fallibility,
        layout: TableLayout,
        drop: Option<fn(*mut u8)>,
    ) -> Result<(), TryReserveError> {
        // Avoid `Option::ok_or_else` because it bloats LLVM IR.
        let new_items = match self.items.checked_add(additional) {
            Some(new_items) => new_items,
            None => return Err(fallibility.capacity_overflow()),
        };
        let full_capacity = bucket_mask_to_capacity(self.bucket_mask);
        if new_items <= full_capacity / 2 {
            // Rehash in-place without re-allocating if we have plenty of spare
            // capacity that is locked up due to DELETED entries.
            self.rehash_in_place(hasher, layout.size, drop);
            Ok(())
        } else {
            // Otherwise, conservatively resize to at least the next size up
            // to avoid churning deletes into frequent rehashes.
            self.resize_inner(
                usize::max(new_items, full_capacity + 1),
                hasher,
                fallibility,
                layout,
            )
        }
    }

    /// Allocates a new table of a different size and moves the contents of the
    /// current table into it.
    ///
    /// This uses dynamic dispatch to reduce the amount of
    /// code generated, but it is eliminated by LLVM optimizations when inlined.
    #[allow(clippy::inline_always)]
    #[inline(always)]
    unsafe fn resize_inner(
        &mut self,
        capacity: usize,
        hasher: &dyn Fn(&mut Self, usize) -> u64,
        fallibility: Fallibility,
        layout: TableLayout,
    ) -> Result<(), TryReserveError> {
        let mut new_table = self.prepare_resize(layout, capacity, fallibility)?;

        // Copy all elements to the new table.
        for i in 0..self.buckets() {
            if !self.is_bucket_full(i) {
                continue;
            }

            // This may panic.
            let hash = hasher(self, i);

            // We can use a simpler version of insert() here since:
            // - there are no DELETED entries.
            // - we know there is enough space in the table.
            // - all elements are unique.
            let (index, _) = new_table.prepare_insert_slot(hash);

            ptr::copy_nonoverlapping(
                self.bucket_ptr(i, layout.size),
                new_table.bucket_ptr(index, layout.size),
                layout.size,
            );
        }

        // We successfully copied all elements without panicking. Now replace
        // self with the new table. The old table will have its memory freed but
        // the items will not be dropped (since they have been moved into the
        // new table).
        mem::swap(self, &mut new_table);

        Ok(())
    }

    /// Rehashes the contents of the table in place (i.e. without changing the
    /// allocation).
    ///
    /// If `hasher` panics then some the table's contents may be lost.
    ///
    /// This uses dynamic dispatch to reduce the amount of
    /// code generated, but it is eliminated by LLVM optimizations when inlined.
    #[allow(clippy::inline_always)]
    #[cfg_attr(feature = "inline-more", inline(always))]
    #[cfg_attr(not(feature = "inline-more"), inline)]
    unsafe fn rehash_in_place(
        &mut self,
        hasher: &dyn Fn(&mut Self, usize) -> u64,
        size_of: usize,
        drop: Option<fn(*mut u8)>,
    ) {
        // If the hash function panics then properly clean up any elements
        // that we haven't rehashed yet. We unfortunately can't preserve the
        // element since we lost their hash and have no way of recovering it
        // without risking another panic.
        self.prepare_rehash_in_place();

        let mut guard = guard(self, move |self_| {
            if let Some(drop) = drop {
                for i in 0..self_.buckets() {
                    if *self_.ctrl(i) == DELETED {
                        self_.set_ctrl(i, EMPTY);
                        drop(self_.bucket_ptr(i, size_of));
                        self_.items -= 1;
                    }
                }
            }
            self_.growth_left = bucket_mask_to_capacity(self_.bucket_mask) - self_.items;
        });

        // At this point, DELETED elements are elements that we haven't
        // rehashed yet. Find them and re-insert them at their ideal
        // position.
        'outer: for i in 0..guard.buckets() {
            if *guard.ctrl(i) != DELETED {
                continue;
            }

            let i_p = guard.bucket_ptr(i, size_of);

            'inner: loop {
                // Hash the current item
                let hash = hasher(*guard, i);

                // Search for a suitable place to put it
                let new_i = guard.find_insert_slot(hash);

                // Probing works by scanning through all of the control
                // bytes in groups, which may not be aligned to the group
                // size. If both the new and old position fall within the
                // same unaligned group, then there is no benefit in moving
                // it and we can just continue to the next item.
                if likely(guard.is_in_same_group(i, new_i, hash)) {
                    guard.set_ctrl_h2(i, hash);
                    continue 'outer;
                }

                let new_i_p = guard.bucket_ptr(new_i, size_of);

                // We are moving the current item to a new position. Write
                // our H2 to the control byte of the new position.
                let prev_ctrl = guard.replace_ctrl_h2(new_i, hash);
                if prev_ctrl == EMPTY {
                    guard.set_ctrl(i, EMPTY);
                    // If the target slot is empty, simply move the current
                    // element into the new slot and clear the old control
                    // byte.
                    ptr::copy_nonoverlapping(i_p, new_i_p, size_of);
                    continue 'outer;
                } else {
                    // If the target slot is occupied, swap the two elements
                    // and then continue processing the element that we just
                    // swapped into the old slot.
                    debug_assert_eq!(prev_ctrl, DELETED);
                    ptr::swap_nonoverlapping(i_p, new_i_p, size_of);
                    continue 'inner;
                }
            }
        }

        guard.growth_left = bucket_mask_to_capacity(guard.bucket_mask) - guard.items;

        mem::forget(guard);
    }

    #[inline]
    unsafe fn free_buckets(&mut self, table_layout: TableLayout) {
        let (ptr, layout) = self.allocation_info(table_layout);
        self.alloc.deallocate(ptr, layout);
    }

    #[inline]
    fn allocation_info(&self, table_layout: TableLayout) -> (NonNull<u8>, Layout) {
        debug_assert!(
            !self.is_empty_singleton(),
            "this function can only be called on non-empty tables"
        );

        // Avoid `Option::unwrap_or_else` because it bloats LLVM IR.
        let (layout, ctrl_offset) = match table_layout.calculate_layout_for(self.buckets()) {
            Some(lco) => lco,
            None => unsafe { hint::unreachable_unchecked() },
        };
        (
            unsafe { NonNull::new_unchecked(self.ctrl.as_ptr().sub(ctrl_offset)) },
            layout,
        )
    }

    #[cfg(feature = "raw")]
    fn allocation_info_or_zero(&self, table_layout: TableLayout) -> (NonNull<u8>, Layout) {
        if self.is_empty_singleton() {
            (NonNull::dangling(), Layout::new::<()>())
        } else {
            self.allocation_info(table_layout)
        }
    }

    /// Marks all table buckets as empty without dropping their contents.
    #[inline]
    fn clear_no_drop(&mut self) {
        if !self.is_empty_singleton() {
            unsafe {
                self.ctrl(0).write_bytes(EMPTY, self.num_ctrl_bytes());
            }
        }
        self.items = 0;
        self.growth_left = bucket_mask_to_capacity(self.bucket_mask);
    }

    /// Erases the [`Bucket`]'s control byte at the given index so that it does not
    /// triggered as full, decreases the `items` of the table and, if it can be done,
    /// increases `self.growth_left`.
    ///
    /// This function does not actually erase / drop the [`Bucket`] itself, i.e. it
    /// does not make any changes to the `data` parts of the table. The caller of this
    /// function must take care to properly drop the `data`, otherwise calling this
    /// function may result in a memory leak.
    ///
    /// # Safety
    ///
    /// You must observe the following safety rules when calling this function:
    ///
    /// * The [`RawTableInner`] has already been allocated;
    ///
    /// * It must be the full control byte at the given position;
    ///
    /// * The `index` must not be greater than the `RawTableInner.bucket_mask`, i.e.
    ///   `index <= RawTableInner.bucket_mask` or, in other words, `(index + 1)` must
    ///   be no greater than the number returned by the function [`RawTableInner::buckets`].
    ///
    /// Calling this function on a table that has not been allocated results in [`undefined behavior`].
    ///
    /// Calling this function on a table with no elements is unspecified, but calling subsequent
    /// functions is likely to result in [`undefined behavior`] due to overflow subtraction
    /// (`self.items -= 1 cause overflow when self.items == 0`).
    ///
    /// See also [`Bucket::as_ptr`] method, for more information about of properly removing
    /// or saving `data element` from / into the [`RawTable`] / [`RawTableInner`].
    ///
    /// [`RawTableInner::buckets`]: RawTableInner::buckets
    /// [`Bucket::as_ptr`]: Bucket::as_ptr
    /// [`undefined behavior`]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    unsafe fn erase(&mut self, index: usize) {
        debug_assert!(self.is_bucket_full(index));

        // This is the same as `index.wrapping_sub(Group::WIDTH) % self.buckets()` because
        // the number of buckets is a power of two, and `self.bucket_mask = self.buckets() - 1`.
        let index_before = index.wrapping_sub(Group::WIDTH) & self.bucket_mask;
        // SAFETY:
        // - The caller must uphold the safety contract for `erase` method;
        // - `index_before` is guaranteed to be in range due to masking with `self.bucket_mask`
        let empty_before = Group::load(self.ctrl(index_before)).match_empty();
        let empty_after = Group::load(self.ctrl(index)).match_empty();

        // Inserting and searching in the map is performed by two key functions:
        //
        // - The `find_insert_slot` function that looks up the index of any `EMPTY` or `DELETED`
        //   slot in a group to be able to insert. If it doesn't find an `EMPTY` or `DELETED`
        //   slot immediately in the first group, it jumps to the next `Group` looking for it,
        //   and so on until it has gone through all the groups in the control bytes.
        //
        // - The `find_inner` function that looks for the index of the desired element by looking
        //   at all the `FULL` bytes in the group. If it did not find the element right away, and
        //   there is no `EMPTY` byte in the group, then this means that the `find_insert_slot`
        //   function may have found a suitable slot in the next group. Therefore, `find_inner`
        //   jumps further, and if it does not find the desired element and again there is no `EMPTY`
        //   byte, then it jumps further, and so on. The search stops only if `find_inner` function
        //   finds the desired element or hits an `EMPTY` slot/byte.
        //
        // Accordingly, this leads to two consequences:
        //
        // - The map must have `EMPTY` slots (bytes);
        //
        // - You can't just mark the byte to be erased as `EMPTY`, because otherwise the `find_inner`
        //   function may stumble upon an `EMPTY` byte before finding the desired element and stop
        //   searching.
        //
        // Thus it is necessary to check all bytes after and before the erased element. If we are in
        // a contiguous `Group` of `FULL` or `DELETED` bytes (the number of `FULL` or `DELETED` bytes
        // before and after is greater than or equal to `Group::WIDTH`), then we must mark our byte as
        // `DELETED` in order for the `find_inner` function to go further. On the other hand, if there
        // is at least one `EMPTY` slot in the `Group`, then the `find_inner` function will still stumble
        // upon an `EMPTY` byte, so we can safely mark our erased byte as `EMPTY` as well.
        //
        // Finally, since `index_before == (index.wrapping_sub(Group::WIDTH) & self.bucket_mask) == index`
        // and given all of the above, tables smaller than the group width (self.buckets() < Group::WIDTH)
        // cannot have `DELETED` bytes.
        //
        // Note that in this context `leading_zeros` refers to the bytes at the end of a group, while
        // `trailing_zeros` refers to the bytes at the beginning of a group.
        let ctrl = if empty_before.leading_zeros() + empty_after.trailing_zeros() >= Group::WIDTH {
            DELETED
        } else {
            self.growth_left += 1;
            EMPTY
        };
        // SAFETY: the caller must uphold the safety contract for `erase` method.
        self.set_ctrl(index, ctrl);
        self.items -= 1;
    }
}

impl<T: Clone, A: Allocator + Clone> Clone for RawTable<T, A> {
    fn clone(&self) -> Self {
        if self.table.is_empty_singleton() {
            Self::new_in(self.table.alloc.clone())
        } else {
            unsafe {
                // Avoid `Result::ok_or_else` because it bloats LLVM IR.
                let new_table = match Self::new_uninitialized(
                    self.table.alloc.clone(),
                    self.table.buckets(),
                    Fallibility::Infallible,
                ) {
                    Ok(table) => table,
                    Err(_) => hint::unreachable_unchecked(),
                };

                // If cloning fails then we need to free the allocation for the
                // new table. However we don't run its drop since its control
                // bytes are not initialized yet.
                let mut guard = guard(ManuallyDrop::new(new_table), |new_table| {
                    new_table.free_buckets();
                });

                guard.clone_from_spec(self);

                // Disarm the scope guard and return the newly created table.
                ManuallyDrop::into_inner(ScopeGuard::into_inner(guard))
            }
        }
    }

    fn clone_from(&mut self, source: &Self) {
        if source.table.is_empty_singleton() {
            *self = Self::new_in(self.table.alloc.clone());
        } else {
            unsafe {
                // Make sure that if any panics occurs, we clear the table and
                // leave it in an empty state.
                let mut self_ = guard(self, |self_| {
                    self_.clear_no_drop();
                });

                // First, drop all our elements without clearing the control
                // bytes. If this panics then the scope guard will clear the
                // table, leaking any elements that were not dropped yet.
                //
                // This leak is unavoidable: we can't try dropping more elements
                // since this could lead to another panic and abort the process.
                self_.drop_elements();

                // If necessary, resize our table to match the source.
                if self_.buckets() != source.buckets() {
                    // Skip our drop by using ptr::write.
                    if !self_.table.is_empty_singleton() {
                        self_.free_buckets();
                    }
                    (&mut **self_ as *mut Self).write(
                        // Avoid `Result::unwrap_or_else` because it bloats LLVM IR.
                        match Self::new_uninitialized(
                            self_.table.alloc.clone(),
                            source.buckets(),
                            Fallibility::Infallible,
                        ) {
                            Ok(table) => table,
                            Err(_) => hint::unreachable_unchecked(),
                        },
                    );
                }

                self_.clone_from_spec(source);

                // Disarm the scope guard if cloning was successful.
                ScopeGuard::into_inner(self_);
            }
        }
    }
}

/// Specialization of `clone_from` for `Copy` types
trait RawTableClone {
    unsafe fn clone_from_spec(&mut self, source: &Self);
}
impl<T: Clone, A: Allocator + Clone> RawTableClone for RawTable<T, A> {
    default_fn! {
        #[cfg_attr(feature = "inline-more", inline)]
        unsafe fn clone_from_spec(&mut self, source: &Self) {
            self.clone_from_impl(source);
        }
    }
}
#[cfg(feature = "nightly")]
impl<T: Copy, A: Allocator + Clone> RawTableClone for RawTable<T, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    unsafe fn clone_from_spec(&mut self, source: &Self) {
        source
            .table
            .ctrl(0)
            .copy_to_nonoverlapping(self.table.ctrl(0), self.table.num_ctrl_bytes());
        source
            .data_start()
            .copy_to_nonoverlapping(self.data_start(), self.table.buckets());

        self.table.items = source.table.items;
        self.table.growth_left = source.table.growth_left;
    }
}

impl<T: Clone, A: Allocator + Clone> RawTable<T, A> {
    /// Common code for clone and clone_from. Assumes:
    /// - `self.buckets() == source.buckets()`.
    /// - Any existing elements have been dropped.
    /// - The control bytes are not initialized yet.
    #[cfg_attr(feature = "inline-more", inline)]
    unsafe fn clone_from_impl(&mut self, source: &Self) {
        // Copy the control bytes unchanged. We do this in a single pass
        source
            .table
            .ctrl(0)
            .copy_to_nonoverlapping(self.table.ctrl(0), self.table.num_ctrl_bytes());

        // The cloning of elements may panic, in which case we need
        // to make sure we drop only the elements that have been
        // cloned so far.
        let mut guard = guard((0, &mut *self), |(index, self_)| {
            if Self::DATA_NEEDS_DROP {
                for i in 0..=*index {
                    if self_.is_bucket_full(i) {
                        self_.bucket(i).drop();
                    }
                }
            }
        });

        for from in source.iter() {
            let index = source.bucket_index(&from);
            let to = guard.1.bucket(index);
            to.write(from.as_ref().clone());

            // Update the index in case we need to unwind.
            guard.0 = index;
        }

        // Successfully cloned all items, no need to clean up.
        mem::forget(guard);

        self.table.items = source.table.items;
        self.table.growth_left = source.table.growth_left;
    }

    /// Variant of `clone_from` to use when a hasher is available.
    #[cfg(feature = "raw")]
    pub fn clone_from_with_hasher(&mut self, source: &Self, hasher: impl Fn(&T) -> u64) {
        // If we have enough capacity in the table, just clear it and insert
        // elements one by one. We don't do this if we have the same number of
        // buckets as the source since we can just copy the contents directly
        // in that case.
        if self.table.buckets() != source.table.buckets()
            && bucket_mask_to_capacity(self.table.bucket_mask) >= source.len()
        {
            self.clear();

            let guard_self = guard(&mut *self, |self_| {
                // Clear the partially copied table if a panic occurs, otherwise
                // items and growth_left will be out of sync with the contents
                // of the table.
                self_.clear();
            });

            unsafe {
                for item in source.iter() {
                    // This may panic.
                    let item = item.as_ref().clone();
                    let hash = hasher(&item);

                    // We can use a simpler version of insert() here since:
                    // - there are no DELETED entries.
                    // - we know there is enough space in the table.
                    // - all elements are unique.
                    let (index, _) = guard_self.table.prepare_insert_slot(hash);
                    guard_self.bucket(index).write(item);
                }
            }

            // Successfully cloned all items, no need to clean up.
            mem::forget(guard_self);

            self.table.items = source.table.items;
            self.table.growth_left -= source.table.items;
        } else {
            self.clone_from(source);
        }
    }
}

impl<T, A: Allocator + Clone + Default> Default for RawTable<T, A> {
    #[inline]
    fn default() -> Self {
        Self::new_in(Default::default())
    }
}

#[cfg(feature = "nightly")]
unsafe impl<#[may_dangle] T, A: Allocator + Clone> Drop for RawTable<T, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn drop(&mut self) {
        if !self.table.is_empty_singleton() {
            unsafe {
                self.drop_elements();
                self.free_buckets();
            }
        }
    }
}
#[cfg(not(feature = "nightly"))]
impl<T, A: Allocator + Clone> Drop for RawTable<T, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn drop(&mut self) {
        if !self.table.is_empty_singleton() {
            unsafe {
                self.drop_elements();
                self.free_buckets();
            }
        }
    }
}

impl<T, A: Allocator + Clone> IntoIterator for RawTable<T, A> {
    type Item = T;
    type IntoIter = RawIntoIter<T, A>;

    #[cfg_attr(feature = "inline-more", inline)]
    fn into_iter(self) -> RawIntoIter<T, A> {
        unsafe {
            let iter = self.iter();
            self.into_iter_from(iter)
        }
    }
}

/// Iterator over a sub-range of a table. Unlike `RawIter` this iterator does
/// not track an item count.
pub(crate) struct RawIterRange<T> {
    // Mask of full buckets in the current group. Bits are cleared from this
    // mask as each element is processed.
    current_group: BitMask,

    // Pointer to the buckets for the current group.
    data: Bucket<T>,

    // Pointer to the next group of control bytes,
    // Must be aligned to the group size.
    next_ctrl: *const u8,

    // Pointer one past the last control byte of this range.
    end: *const u8,
}

impl<T> RawIterRange<T> {
    /// Returns a `RawIterRange` covering a subset of a table.
    ///
    /// The control byte address must be aligned to the group size.
    #[cfg_attr(feature = "inline-more", inline)]
    unsafe fn new(ctrl: *const u8, data: Bucket<T>, len: usize) -> Self {
        debug_assert_ne!(len, 0);
        debug_assert_eq!(ctrl as usize % Group::WIDTH, 0);
        let end = ctrl.add(len);

        // Load the first group and advance ctrl to point to the next group
        let current_group = Group::load_aligned(ctrl).match_full();
        let next_ctrl = ctrl.add(Group::WIDTH);

        Self {
            current_group,
            data,
            next_ctrl,
            end,
        }
    }

    /// Splits a `RawIterRange` into two halves.
    ///
    /// Returns `None` if the remaining range is smaller than or equal to the
    /// group width.
    #[cfg_attr(feature = "inline-more", inline)]
    #[cfg(feature = "rayon")]
    pub(crate) fn split(mut self) -> (Self, Option<RawIterRange<T>>) {
        unsafe {
            if self.end <= self.next_ctrl {
                // Nothing to split if the group that we are current processing
                // is the last one.
                (self, None)
            } else {
                // len is the remaining number of elements after the group that
                // we are currently processing. It must be a multiple of the
                // group size (small tables are caught by the check above).
                let len = offset_from(self.end, self.next_ctrl);
                debug_assert_eq!(len % Group::WIDTH, 0);

                // Split the remaining elements into two halves, but round the
                // midpoint down in case there is an odd number of groups
                // remaining. This ensures that:
                // - The tail is at least 1 group long.
                // - The split is roughly even considering we still have the
                //   current group to process.
                let mid = (len / 2) & !(Group::WIDTH - 1);

                let tail = Self::new(
                    self.next_ctrl.add(mid),
                    self.data.next_n(Group::WIDTH).next_n(mid),
                    len - mid,
                );
                debug_assert_eq!(
                    self.data.next_n(Group::WIDTH).next_n(mid).ptr,
                    tail.data.ptr
                );
                debug_assert_eq!(self.end, tail.end);
                self.end = self.next_ctrl.add(mid);
                debug_assert_eq!(self.end.add(Group::WIDTH), tail.next_ctrl);
                (self, Some(tail))
            }
        }
    }

    /// # Safety
    /// If DO_CHECK_PTR_RANGE is false, caller must ensure that we never try to iterate
    /// after yielding all elements.
    #[cfg_attr(feature = "inline-more", inline)]
    unsafe fn next_impl<const DO_CHECK_PTR_RANGE: bool>(&mut self) -> Option<Bucket<T>> {
        loop {
            if let Some(index) = self.current_group.lowest_set_bit() {
                self.current_group = self.current_group.remove_lowest_bit();
                return Some(self.data.next_n(index));
            }

            if DO_CHECK_PTR_RANGE && self.next_ctrl >= self.end {
                return None;
            }

            // We might read past self.end up to the next group boundary,
            // but this is fine because it only occurs on tables smaller
            // than the group size where the trailing control bytes are all
            // EMPTY. On larger tables self.end is guaranteed to be aligned
            // to the group size (since tables are power-of-two sized).
            self.current_group = Group::load_aligned(self.next_ctrl).match_full();
            self.data = self.data.next_n(Group::WIDTH);
            self.next_ctrl = self.next_ctrl.add(Group::WIDTH);
        }
    }
}

// We make raw iterators unconditionally Send and Sync, and let the PhantomData
// in the actual iterator implementations determine the real Send/Sync bounds.
unsafe impl<T> Send for RawIterRange<T> {}
unsafe impl<T> Sync for RawIterRange<T> {}

impl<T> Clone for RawIterRange<T> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
            next_ctrl: self.next_ctrl,
            current_group: self.current_group,
            end: self.end,
        }
    }
}

impl<T> Iterator for RawIterRange<T> {
    type Item = Bucket<T>;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<Bucket<T>> {
        unsafe {
            // SAFETY: We set checker flag to true.
            self.next_impl::<true>()
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        // We don't have an item count, so just guess based on the range size.
        let remaining_buckets = if self.end > self.next_ctrl {
            unsafe { offset_from(self.end, self.next_ctrl) }
        } else {
            0
        };

        // Add a group width to include the group we are currently processing.
        (0, Some(Group::WIDTH + remaining_buckets))
    }
}

impl<T> FusedIterator for RawIterRange<T> {}

/// Iterator which returns a raw pointer to every full bucket in the table.
///
/// For maximum flexibility this iterator is not bound by a lifetime, but you
/// must observe several rules when using it:
/// - You must not free the hash table while iterating (including via growing/shrinking).
/// - It is fine to erase a bucket that has been yielded by the iterator.
/// - Erasing a bucket that has not yet been yielded by the iterator may still
///   result in the iterator yielding that bucket (unless `reflect_remove` is called).
/// - It is unspecified whether an element inserted after the iterator was
///   created will be yielded by that iterator (unless `reflect_insert` is called).
/// - The order in which the iterator yields bucket is unspecified and may
///   change in the future.
pub struct RawIter<T> {
    pub(crate) iter: RawIterRange<T>,
    items: usize,
}

impl<T> RawIter<T> {
    const DATA_NEEDS_DROP: bool = mem::needs_drop::<T>();

    /// Refresh the iterator so that it reflects a removal from the given bucket.
    ///
    /// For the iterator to remain valid, this method must be called once
    /// for each removed bucket before `next` is called again.
    ///
    /// This method should be called _before_ the removal is made. It is not necessary to call this
    /// method if you are removing an item that this iterator yielded in the past.
    #[cfg(feature = "raw")]
    pub fn reflect_remove(&mut self, b: &Bucket<T>) {
        self.reflect_toggle_full(b, false);
    }

    /// Refresh the iterator so that it reflects an insertion into the given bucket.
    ///
    /// For the iterator to remain valid, this method must be called once
    /// for each insert before `next` is called again.
    ///
    /// This method does not guarantee that an insertion of a bucket with a greater
    /// index than the last one yielded will be reflected in the iterator.
    ///
    /// This method should be called _after_ the given insert is made.
    #[cfg(feature = "raw")]
    pub fn reflect_insert(&mut self, b: &Bucket<T>) {
        self.reflect_toggle_full(b, true);
    }

    /// Refresh the iterator so that it reflects a change to the state of the given bucket.
    #[cfg(feature = "raw")]
    fn reflect_toggle_full(&mut self, b: &Bucket<T>, is_insert: bool) {
        unsafe {
            if b.as_ptr() > self.iter.data.as_ptr() {
                // The iterator has already passed the bucket's group.
                // So the toggle isn't relevant to this iterator.
                return;
            }

            if self.iter.next_ctrl < self.iter.end
                && b.as_ptr() <= self.iter.data.next_n(Group::WIDTH).as_ptr()
            {
                // The iterator has not yet reached the bucket's group.
                // We don't need to reload anything, but we do need to adjust the item count.

                if cfg!(debug_assertions) {
                    // Double-check that the user isn't lying to us by checking the bucket state.
                    // To do that, we need to find its control byte. We know that self.iter.data is
                    // at self.iter.next_ctrl - Group::WIDTH, so we work from there:
                    let offset = offset_from(self.iter.data.as_ptr(), b.as_ptr());
                    let ctrl = self.iter.next_ctrl.sub(Group::WIDTH).add(offset);
                    // This method should be called _before_ a removal, or _after_ an insert,
                    // so in both cases the ctrl byte should indicate that the bucket is full.
                    assert!(is_full(*ctrl));
                }

                if is_insert {
                    self.items += 1;
                } else {
                    self.items -= 1;
                }

                return;
            }

            // The iterator is at the bucket group that the toggled bucket is in.
            // We need to do two things:
            //
            //  - Determine if the iterator already yielded the toggled bucket.
            //    If it did, we're done.
            //  - Otherwise, update the iterator cached group so that it won't
            //    yield a to-be-removed bucket, or _will_ yield a to-be-added bucket.
            //    We'll also need to update the item count accordingly.
            if let Some(index) = self.iter.current_group.lowest_set_bit() {
                let next_bucket = self.iter.data.next_n(index);
                if b.as_ptr() > next_bucket.as_ptr() {
                    // The toggled bucket is "before" the bucket the iterator would yield next. We
                    // therefore don't need to do anything --- the iterator has already passed the
                    // bucket in question.
                    //
                    // The item count must already be correct, since a removal or insert "prior" to
                    // the iterator's position wouldn't affect the item count.
                } else {
                    // The removed bucket is an upcoming bucket. We need to make sure it does _not_
                    // get yielded, and also that it's no longer included in the item count.
                    //
                    // NOTE: We can't just reload the group here, both since that might reflect
                    // inserts we've already passed, and because that might inadvertently unset the
                    // bits for _other_ removals. If we do that, we'd have to also decrement the
                    // item count for those other bits that we unset. But the presumably subsequent
                    // call to reflect for those buckets might _also_ decrement the item count.
                    // Instead, we _just_ flip the bit for the particular bucket the caller asked
                    // us to reflect.
                    let our_bit = offset_from(self.iter.data.as_ptr(), b.as_ptr());
                    let was_full = self.iter.current_group.flip(our_bit);
                    debug_assert_ne!(was_full, is_insert);

                    if is_insert {
                        self.items += 1;
                    } else {
                        self.items -= 1;
                    }

                    if cfg!(debug_assertions) {
                        if b.as_ptr() == next_bucket.as_ptr() {
                            // The removed bucket should no longer be next
                            debug_assert_ne!(self.iter.current_group.lowest_set_bit(), Some(index));
                        } else {
                            // We should not have changed what bucket comes next.
                            debug_assert_eq!(self.iter.current_group.lowest_set_bit(), Some(index));
                        }
                    }
                }
            } else {
                // We must have already iterated past the removed item.
            }
        }
    }

    unsafe fn drop_elements(&mut self) {
        if Self::DATA_NEEDS_DROP && self.len() != 0 {
            for item in self {
                item.drop();
            }
        }
    }
}

impl<T> Clone for RawIter<T> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
            items: self.items,
        }
    }
}

impl<T> Iterator for RawIter<T> {
    type Item = Bucket<T>;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<Bucket<T>> {
        // Inner iterator iterates over buckets
        // so it can do unnecessary work if we already yielded all items.
        if self.items == 0 {
            return None;
        }

        let nxt = unsafe {
            // SAFETY: We check number of items to yield using `items` field.
            self.iter.next_impl::<false>()
        };

        debug_assert!(nxt.is_some());
        self.items -= 1;

        nxt
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.items, Some(self.items))
    }
}

impl<T> ExactSizeIterator for RawIter<T> {}
impl<T> FusedIterator for RawIter<T> {}

/// Iterator which consumes a table and returns elements.
pub struct RawIntoIter<T, A: Allocator + Clone = Global> {
    iter: RawIter<T>,
    allocation: Option<(NonNull<u8>, Layout)>,
    marker: PhantomData<T>,
    alloc: A,
}

impl<T, A: Allocator + Clone> RawIntoIter<T, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn iter(&self) -> RawIter<T> {
        self.iter.clone()
    }
}

unsafe impl<T, A: Allocator + Clone> Send for RawIntoIter<T, A>
where
    T: Send,
    A: Send,
{
}
unsafe impl<T, A: Allocator + Clone> Sync for RawIntoIter<T, A>
where
    T: Sync,
    A: Sync,
{
}

#[cfg(feature = "nightly")]
unsafe impl<#[may_dangle] T, A: Allocator + Clone> Drop for RawIntoIter<T, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn drop(&mut self) {
        unsafe {
            // Drop all remaining elements
            self.iter.drop_elements();

            // Free the table
            if let Some((ptr, layout)) = self.allocation {
                self.alloc.deallocate(ptr, layout);
            }
        }
    }
}
#[cfg(not(feature = "nightly"))]
impl<T, A: Allocator + Clone> Drop for RawIntoIter<T, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn drop(&mut self) {
        unsafe {
            // Drop all remaining elements
            self.iter.drop_elements();

            // Free the table
            if let Some((ptr, layout)) = self.allocation {
                self.alloc.deallocate(ptr, layout);
            }
        }
    }
}

impl<T, A: Allocator + Clone> Iterator for RawIntoIter<T, A> {
    type Item = T;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<T> {
        unsafe { Some(self.iter.next()?.read()) }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T, A: Allocator + Clone> ExactSizeIterator for RawIntoIter<T, A> {}
impl<T, A: Allocator + Clone> FusedIterator for RawIntoIter<T, A> {}

/// Iterator which consumes elements without freeing the table storage.
pub struct RawDrain<'a, T, A: Allocator + Clone = Global> {
    iter: RawIter<T>,

    // The table is moved into the iterator for the duration of the drain. This
    // ensures that an empty table is left if the drain iterator is leaked
    // without dropping.
    table: ManuallyDrop<RawTable<T, A>>,
    orig_table: NonNull<RawTable<T, A>>,

    // We don't use a &'a mut RawTable<T> because we want RawDrain to be
    // covariant over T.
    marker: PhantomData<&'a RawTable<T, A>>,
}

impl<T, A: Allocator + Clone> RawDrain<'_, T, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn iter(&self) -> RawIter<T> {
        self.iter.clone()
    }
}

unsafe impl<T, A: Allocator + Copy> Send for RawDrain<'_, T, A>
where
    T: Send,
    A: Send,
{
}
unsafe impl<T, A: Allocator + Copy> Sync for RawDrain<'_, T, A>
where
    T: Sync,
    A: Sync,
{
}

impl<T, A: Allocator + Clone> Drop for RawDrain<'_, T, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    fn drop(&mut self) {
        unsafe {
            // Drop all remaining elements. Note that this may panic.
            self.iter.drop_elements();

            // Reset the contents of the table now that all elements have been
            // dropped.
            self.table.clear_no_drop();

            // Move the now empty table back to its original location.
            self.orig_table
                .as_ptr()
                .copy_from_nonoverlapping(&*self.table, 1);
        }
    }
}

impl<T, A: Allocator + Clone> Iterator for RawDrain<'_, T, A> {
    type Item = T;

    #[cfg_attr(feature = "inline-more", inline)]
    fn next(&mut self) -> Option<T> {
        unsafe {
            let item = self.iter.next()?;
            Some(item.read())
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T, A: Allocator + Clone> ExactSizeIterator for RawDrain<'_, T, A> {}
impl<T, A: Allocator + Clone> FusedIterator for RawDrain<'_, T, A> {}

/// Iterator over occupied buckets that could match a given hash.
///
/// `RawTable` only stores 7 bits of the hash value, so this iterator may return
/// items that have a hash value different than the one provided. You should
/// always validate the returned values before using them.
pub struct RawIterHash<'a, T, A: Allocator + Clone = Global> {
    inner: RawIterHashInner<'a, A>,
    _marker: PhantomData<T>,
}

struct RawIterHashInner<'a, A: Allocator + Clone> {
    table: &'a RawTableInner<A>,

    // The top 7 bits of the hash.
    h2_hash: u8,

    // The sequence of groups to probe in the search.
    probe_seq: ProbeSeq,

    group: Group,

    // The elements within the group with a matching h2-hash.
    bitmask: BitMaskIter,
}

impl<'a, T, A: Allocator + Clone> RawIterHash<'a, T, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    #[cfg(feature = "raw")]
    fn new(table: &'a RawTable<T, A>, hash: u64) -> Self {
        RawIterHash {
            inner: RawIterHashInner::new(&table.table, hash),
            _marker: PhantomData,
        }
    }
}
impl<'a, A: Allocator + Clone> RawIterHashInner<'a, A> {
    #[cfg_attr(feature = "inline-more", inline)]
    #[cfg(feature = "raw")]
    fn new(table: &'a RawTableInner<A>, hash: u64) -> Self {
        unsafe {
            let h2_hash = h2(hash);
            let probe_seq = table.probe_seq(hash);
            let group = Group::load(table.ctrl(probe_seq.pos));
            let bitmask = group.match_byte(h2_hash).into_iter();

            RawIterHashInner {
                table,
                h2_hash,
                probe_seq,
                group,
                bitmask,
            }
        }
    }
}

impl<'a, T, A: Allocator + Clone> Iterator for RawIterHash<'a, T, A> {
    type Item = Bucket<T>;

    fn next(&mut self) -> Option<Bucket<T>> {
        unsafe {
            match self.inner.next() {
                Some(index) => Some(self.inner.table.bucket(index)),
                None => None,
            }
        }
    }
}

impl<'a, A: Allocator + Clone> Iterator for RawIterHashInner<'a, A> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            loop {
                if let Some(bit) = self.bitmask.next() {
                    let index = (self.probe_seq.pos + bit) & self.table.bucket_mask;
                    return Some(index);
                }
                if likely(self.group.match_empty().any_bit_set()) {
                    return None;
                }
                self.probe_seq.move_next(self.table.bucket_mask);
                self.group = Group::load(self.table.ctrl(self.probe_seq.pos));
                self.bitmask = self.group.match_byte(self.h2_hash).into_iter();
            }
        }
    }
}

#[cfg(test)]
mod test_map {
    use super::*;

    fn rehash_in_place<T>(table: &mut RawTable<T>, hasher: impl Fn(&T) -> u64) {
        unsafe {
            table.table.rehash_in_place(
                &|table, index| hasher(table.bucket::<T>(index).as_ref()),
                mem::size_of::<T>(),
                if mem::needs_drop::<T>() {
                    Some(mem::transmute(ptr::drop_in_place::<T> as unsafe fn(*mut T)))
                } else {
                    None
                },
            );
        }
    }

    #[test]
    fn rehash() {
        let mut table = RawTable::new();
        let hasher = |i: &u64| *i;
        for i in 0..100 {
            table.insert(i, i, hasher);
        }

        for i in 0..100 {
            unsafe {
                assert_eq!(table.find(i, |x| *x == i).map(|b| b.read()), Some(i));
            }
            assert!(table.find(i + 100, |x| *x == i + 100).is_none());
        }

        rehash_in_place(&mut table, hasher);

        for i in 0..100 {
            unsafe {
                assert_eq!(table.find(i, |x| *x == i).map(|b| b.read()), Some(i));
            }
            assert!(table.find(i + 100, |x| *x == i + 100).is_none());
        }
    }
}
