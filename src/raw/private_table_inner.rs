//! This module contain declaration of non-generic [`RawTableInner`] which allows
//! functions to be instantiated only once regardless of how many different key-value
//! types are used.
//!
//! The purpose of this module is to prevent other parts of the crate from changing
//! the field containing the pointer to the allocated memory and the field containing
//! information about the size of the allocated memory.
//!
//! Therefore, this module contains only the basic API for allocating/deallocating
//! a table and accessing table fields. All other APIs must not be included in this
//! module and must be declared in the parent module.

use super::{
    bucket_mask_to_capacity, do_alloc, Allocator, Fallibility, Group, Layout, TryReserveError,
};
use core::hint;
use core::ptr::NonNull;

/// Non-generic part of `RawTable` which allows functions to be instantiated only once regardless
/// of how many different key-value types are used.
///
/// # Memory Layout
///
/// The current table implementation is designed to implement the smallest possible structure size.
/// The memory layout for the allocated table looks like this (we start counting from "0", so that
/// in the expression T[n], the "n" index actually one less than the "buckets" number of the
/// `RawTableInner`, i.e. "n = RawTableInner::buckets() - 1"):
///
/// ```none
///                           `ctrl: NonNull<u8>` points here (to the end of `T0`
///                            and to the start of `CT0`)
///                              ∨
/// [Padding], T_n, ..., T1, T0, |CT0, CT1, ..., CT_n|, CTa_0, CTa_1, ..., CTa_m
///                              \_________  ________/  \__________  __________/
///                                        \/                      \/
///                             `n = bucket_mask, i.e.    additional control bytes
///                     `RawTableInner::buckets() - 1`     `m = Group::WIDTH - 1`
///
/// where: T0...T_n  - our stored data;
///        CT0...CT_n - control bytes or metadata for `data`;
///        n - one less than the number of buckets in the `RawIndexTable`;
///        CTa_0...CTa_m - additional control bytes, where `m = Group::WIDTH - 1` (so that the search
///                        with loading `Group` bytes from the heap works properly, even if the result
///                        of `h1(hash) & self.bucket_mask` is equal to `self.bucket_mask`). See also
///                        `RawTableInner::set_ctrl` function.
/// ```
///
/// The memory layout for a table that has not been allocated looks like this:
///
/// ```none
///
///  `ctrl: NonNull<u8>` points here (to the start of `CT0`)
///    ∨
///    |CTa_0, CTa_1, ..., CTa_m
///     \__________  __________/
///                \/
///      additional control bytes
///       `m = Group::WIDTH - 1`
/// ```
///
/// # Safety requirements
///
/// All [`RawTableInner`] methods are made on the assumption that the `ctrl` and `bucket_mask` fields
/// will remain unchanged throughout the entire life of current `RawTableInner` instance.
///
/// The requirements for these fields are listed below, and are provided by the `RawTableInner::new`
/// and `RawTableInner::new_uninitialized` functions by free, so users do not need to manually change
/// these fields.
///
/// * `bucket_mask` must be one less than the total number of buckets in the table. The total number
///   of buckets (`bucket_mask + 1`) must be a power of two. In case the table has not been allocated,
///   `bucket_mask` must be equal to zero (`bucket_mask = 0`);
///
/// * `ctrl` must be [valid] for reads for the table that has not been allocated, and must be [valid]
///   for reads and writes for the allocated table.
///
/// * `ctrl` must be properly aligned to `usize::max(mem::align_of::<T>(), Group::WIDTH)`, where `T`
///   is the type stored in the table;
///
/// * `ctrl` must point to the start of array of control bytes and at the same time must point to one
///   past last `data` element in the the table as viewed from the start point of the allocation.
///
/// [valid]: https://doc.rust-lang.org/std/ptr/index.html#safety
pub(super) struct RawTableInner {
    // Mask to get an index from a hash value. The value is one less than the
    // number of buckets in the table.
    // This field must not be exposed in the parent module because it must remain
    // unchanged for the entire life of the `RawTableInner` instance.
    bucket_mask: usize,

    // Pointer to allocated memory. See memoty layout above.
    // This field must not be exposed in the parent module because it must remain
    // unchanged for the entire life of the `RawTableInner` instance.
    ctrl: NonNull<u8>,

    // Number of elements that can be inserted before we need to grow the table
    pub(super) growth_left: usize,

    // Number of elements in the table, only really used by len()
    pub(super) items: usize,
}

impl RawTableInner {
    pub(super) const NEW: Self = RawTableInner::new();

    /// Creates a new empty hash table without allocating any memory.
    ///
    /// In effect this returns a table containing only `[u8; Group::WIDTH]` array
    /// of control bytes.
    ///
    /// Since we set `bucket_mask` to the lowest possible value, that is, we set
    /// `bucket_mask` to zero, mathematically, this can be thought of as returning
    /// a table with exactly 1 bucket. However, this is ok, since this **imaginary**
    /// bucket will never be accessed due to our load factor, which forces us to
    /// always have at least 1 free bucket.
    #[inline]
    pub(super) const fn new() -> Self {
        Self {
            // Be careful to cast the entire slice to a raw pointer.
            ctrl: unsafe { NonNull::new_unchecked(Group::static_empty() as *const _ as *mut u8) },
            bucket_mask: 0,
            items: 0,
            growth_left: 0,
        }
    }

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
    /// [`EMPTY`]: super::EMPTY
    #[cfg_attr(feature = "inline-more", inline)]
    pub(super) unsafe fn new_uninitialized<A>(
        alloc: &A,
        table_layout: TableLayout,
        buckets: usize,
        fallibility: Fallibility,
    ) -> Result<Self, TryReserveError>
    where
        A: Allocator,
    {
        debug_assert!(buckets.is_power_of_two());

        // Avoid `Option::ok_or_else` because it bloats LLVM IR.
        let (layout, ctrl_offset) = match table_layout.calculate_layout_for(buckets) {
            Some(lco) => lco,
            None => return Err(fallibility.capacity_overflow()),
        };

        let ptr: NonNull<u8> = match do_alloc(alloc, layout) {
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
        })
    }

    /// Returns the mask to get an index from a hash value.
    ///
    /// The value is one less than the number of buckets in the table.
    #[inline(always)]
    pub(super) fn bucket_mask(&self) -> usize {
        self.bucket_mask
    }

    /// Returns pointer to one past last `data` element in the the table as viewed from
    /// the start point of the allocation (convenience for `self.ctrl.cast()`).
    ///
    /// This function actually returns a pointer to the end of the `data element` at
    /// index "0" (zero).
    ///
    /// The caller must ensure that the `RawTableInner` outlives the returned [`NonNull<T>`],
    /// otherwise using it may result in [`undefined behavior`].
    ///
    /// # Note
    ///
    /// The type `T` must be the actual type of the elements stored in the table, otherwise
    /// using the returned [`NonNull<T>`] may result in [`undefined behavior`].
    ///
    /// ```none
    ///                        `table.data_end::<T>()` returns pointer that points here
    ///                        (to the end of `T0`)
    ///                          ∨
    /// [Pad], T_n, ..., T1, T0, |CT0, CT1, ..., CT_n|, CTa_0, CTa_1, ..., CTa_m
    ///                           \________  ________/
    ///                                    \/
    ///       `n = buckets - 1`, i.e. `RawTableInner::buckets() - 1`
    ///
    /// where: T0...T_n  - our stored data;
    ///        CT0...CT_n - control bytes or metadata for `data`.
    ///        CTa_0...CTa_m - additional control bytes, where `m = Group::WIDTH - 1` (so that the search
    ///                        with loading `Group` bytes from the heap works properly, even if the result
    ///                        of `h1(hash) & self.bucket_mask` is equal to `self.bucket_mask`). See also
    ///                        `RawTableInner::set_ctrl` function.
    ///
    /// P.S. `h1(hash) & self.bucket_mask` is the same as `hash as usize % self.buckets()` because the number
    /// of buckets is a power of two, and `self.bucket_mask = self.buckets() - 1`.
    /// ```
    ///
    /// [`undefined behavior`]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub(super) fn data_end<T>(&self) -> NonNull<T> {
        unsafe {
            // SAFETY: `self.ctrl` is `NonNull`, so casting it is safe
            NonNull::new_unchecked(self.ctrl.as_ptr().cast())
        }
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
    /// [`Bucket::as_ptr()`]: super::Bucket::as_ptr()
    /// [`Undefined Behavior`]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    /// [`RawTable`]: super::RawTable
    #[inline]
    pub(super) unsafe fn ctrl(&self, index: usize) -> *mut u8 {
        debug_assert!(index < self.num_ctrl_bytes());
        // SAFETY: The caller must uphold the safety rules for the [`RawTableInner::ctrl`]
        self.ctrl.as_ptr().add(index)
    }

    /// Returns the total number of buckets in the table. The returned value
    /// is a power of two.
    #[inline(always)]
    pub(super) fn buckets(&self) -> usize {
        self.bucket_mask + 1
    }

    /// Returns the total number of control bytes in the table. The returned value
    /// is greater than the number of buckets by [`Group::WIDTH`](Group::WIDTH).
    #[inline]
    pub(super) fn num_ctrl_bytes(&self) -> usize {
        self.bucket_mask + 1 + Group::WIDTH
    }

    /// Returns [`true`] if the table owns allocated memory.
    ///
    /// Mathematically, we check whether this table is a table with exactly one bucket
    /// (see [`RawTableInner::new()`]).
    ///
    /// [`RawTableInner::new()`]: RawTableInner::new
    #[inline]
    pub(super) fn is_empty_singleton(&self) -> bool {
        self.bucket_mask == 0
    }

    /// Deallocates the table without dropping any entries.
    ///
    /// # Note
    ///
    /// This function must be called only after [`drop_elements`](RawTableInner::drop_elements),
    /// else it can lead to leaking of memory. Also calling this function automatically
    /// makes invalid (dangling) all instances of buckets ([`Bucket`]) and makes invalid
    /// (dangling) the `ctrl` field of the table.
    ///
    /// # Safety
    ///
    /// If any of the following conditions are violated, the result is [`Undefined Behavior`]:
    ///
    /// * The [`RawTableInner`] has already been allocated;
    ///
    /// * The `alloc` must be the same [`Allocator`] as the `Allocator` that was used
    ///   to allocate this table.
    ///
    /// * The `table_layout` must be the same [`TableLayout`] as the `TableLayout` that was used
    ///   to allocate this table.
    ///
    /// See also [`GlobalAlloc::dealloc`] or [`Allocator::deallocate`] for more  information.
    ///
    /// [`Undefined Behavior`]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    /// [`GlobalAlloc::dealloc`]: https://doc.rust-lang.org/alloc/alloc/trait.GlobalAlloc.html#tymethod.dealloc
    /// [`Allocator::deallocate`]: https://doc.rust-lang.org/alloc/alloc/trait.Allocator.html#tymethod.deallocate
    /// [`Bucket`]: super::Bucket
    #[inline]
    pub(super) unsafe fn free_buckets<A>(&mut self, alloc: &A, table_layout: TableLayout)
    where
        A: Allocator,
    {
        // SAFETY: The caller must uphold the safety contract for `free_buckets`
        // method.
        let (ptr, layout) = self.allocation_info(table_layout);
        alloc.deallocate(ptr, layout);
    }

    /// Returns a pointer to the allocated memory and the layout that was used to
    /// allocate the table.
    ///
    /// # Safety
    ///
    /// Caller of this function must observe the following safety rules:
    ///
    /// * The [`RawTableInner`] has already been allocated, otherwise
    ///   calling this function results in [`undefined behavior`]
    ///
    /// * The `table_layout` must be the same [`TableLayout`] as the `TableLayout`
    ///   that was used to allocate this table. Failure to comply with this condition
    ///   may result in [`undefined behavior`].
    ///
    /// See also [`GlobalAlloc::dealloc`] or [`Allocator::deallocate`] for more  information.
    ///
    /// [`undefined behavior`]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    /// [`GlobalAlloc::dealloc`]: https://doc.rust-lang.org/alloc/alloc/trait.GlobalAlloc.html#tymethod.dealloc
    /// [`Allocator::deallocate`]: https://doc.rust-lang.org/alloc/alloc/trait.Allocator.html#tymethod.deallocate
    #[inline]
    pub(super) unsafe fn allocation_info(
        &self,
        table_layout: TableLayout,
    ) -> (NonNull<u8>, Layout) {
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
            // SAFETY: The caller must uphold the safety contract for `allocation_info` method.
            unsafe { NonNull::new_unchecked(self.ctrl.as_ptr().sub(ctrl_offset)) },
            layout,
        )
    }

    /// Returns a pointer to the allocated memory and the layout that was used to
    /// allocate the table. If [`RawTableInner`] has not been allocated, this
    /// function return `dangling` pointer and `()` (unit) layout.
    ///
    /// # Safety
    ///
    /// The `table_layout` must be the same [`TableLayout`] as the `TableLayout`
    /// that was used to allocate this table. Failure to comply with this condition
    /// may result in [`undefined behavior`].
    ///
    /// See also [`GlobalAlloc::dealloc`] or [`Allocator::deallocate`] for more  information.
    ///
    /// [`undefined behavior`]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    /// [`GlobalAlloc::dealloc`]: https://doc.rust-lang.org/alloc/alloc/trait.GlobalAlloc.html#tymethod.dealloc
    /// [`Allocator::deallocate`]: https://doc.rust-lang.org/alloc/alloc/trait.Allocator.html#tymethod.deallocate
    #[cfg(feature = "raw")]
    pub(super) unsafe fn allocation_info_or_zero(
        &self,
        table_layout: TableLayout,
    ) -> (NonNull<u8>, Layout) {
        if self.is_empty_singleton() {
            (NonNull::dangling(), Layout::new::<()>())
        } else {
            // SAFETY:
            // 1. We have checked that our table is allocated.
            // 2. The caller ensures that `table_layout` matches the [`TableLayout`]
            // that was used to allocate this table.
            unsafe { self.allocation_info(table_layout) }
        }
    }
}

/// Helper which allows the max calculation for ctrl_align to be statically computed for each T
/// while keeping the rest of `calculate_layout_for` independent of `T`
#[derive(Copy, Clone)]
pub(super) struct TableLayout {
    // Size of `T` type stored in the table (RawTable / RawTableInner)
    size: usize,
    // Max align (`usize::max(mem::align_of::<T>(), Group::WIDTH)`), where
    // `T` is the type stored in the table;
    ctrl_align: usize,
}

impl TableLayout {
    /// Returns a new [`TableLayout`] instance.
    #[inline]
    pub(super) const fn new<T>() -> Self {
        let layout = Layout::new::<T>();
        Self {
            size: layout.size(),
            // We use manual comparison because Ord::max is not a constant function.
            ctrl_align: if layout.align() > Group::WIDTH {
                layout.align()
            } else {
                Group::WIDTH
            },
        }
    }

    /// Returns the [`Layout`] of memory to allocate/deallocate [`RawTableInner`], as well as the
    /// `ctrl_offset: usize` needed to calculate the `ctrl: NonNull<u8>` pointer to point to the
    /// the start of array of control bytes while at the same time point to one past last `data`
    /// element in the the table as viewed from the start point of the allocation.
    #[inline]
    fn calculate_layout_for(self, buckets: usize) -> Option<(Layout, usize)> {
        debug_assert!(buckets.is_power_of_two());

        // Rough model of our memory looks like as shown below (we start counting from "0", so that
        // in the expression T[n], the "n" index actually one less than the given "buckets" number,
        // i.e. "n = buckets - 1"). It only reflects the amount of allocated memory, not the actual
        // arrangement of the elements. See `RawTableInner` memory layout for correct information.
        //
        //                          ctrl_offset points here
        //                               ∨
        // |T0, T1, ..., T_n, [Padding], |CT0, CT1, ..., CT_n, |CTa_0, CTa_1, ..., CTa_m
        // \____________  ____________/  \________  ________/  \__________  ___________/
        //              \/                        \/                      \/
        //     all data length with      control bytes length   additional control bytes
        //  alignment (size * buckets)                           `m = Group::WIDTH - 1`
        // \___________________________________  ______________________________________/
        //                                     \/
        //                      len (length of all allocation)
        //                          where `n = buckets - 1`

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

    /// Returns the size of the `T` type that was used to create this [`TableLayout`] instance.
    #[inline(always)]
    pub(super) fn size(&self) -> usize {
        self.size
    }
}
