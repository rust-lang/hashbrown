use crate::util::{likely, unlikely};
use core::{marker::PhantomData, ptr::NonNull, slice};

use super::{BitMaskIter, Group, Tag};

/// Probe over an individual group, returned by [`Probe`].
#[derive(Clone)]
pub(crate) struct GroupProbe {
    /// Original control pointer.
    ctrl: NonNull<Tag>,

    /// Original search tag.
    hash_tag: Tag,

    /// Group being probed.
    group: Group,

    /// Index of the group.
    index: usize,

    /// Number of buckets, minus one.
    bucket_mask: usize,
}
impl GroupProbe {
    /// Checks whether the group contains any empty slots.
    ///
    /// This is equivalent to `empty().is_some()`.
    #[inline]
    pub(crate) fn has_empty(&self) -> bool {
        self.group.match_empty().any_bit_set()
    }

    /// Finds an empty slot in the group to insert a new item.
    #[inline]
    pub(crate) fn empty(&self) -> Option<usize> {
        let bit = self.group.match_empty_or_deleted().lowest_set_bit();
        if likely(bit.is_some()) {
            // SAFETY: We have some.
            let bit = unsafe { bit.unwrap_unchecked() };

            // This is the same as `(probe_seq.pos + bit) % self.buckets()` because the number
            // of buckets is a power of two, and `self.bucket_mask = self.buckets() - 1`.
            let mut index = (self.index + bit) & self.bucket_mask;

            // In tables smaller than the group width (`self.buckets() < Group::WIDTH`), trailing control
            // bytes outside the range of the table are filled with [`Tag::EMPTY`] entries. These will unfortunately
            // trigger a match because the `Some(bit)` returned by `group.match_empty_or_deleted().lowest_set_bit()`
            // after masking (`(probe_seq.pos + bit) & self.bucket_mask`) may point to a full bucket that is already
            // occupied. We detect this situation here and perform a second scan starting at the beginning of the table.
            // This second scan is guaranteed to find an empty slot (due to the load factor) before hitting the
            // trailing control bytes (containing [`Tag::EMPTY`] bytes).

            // SAFETY: By masking the index with bucket_mask, we guarantee this is in bounds.
            let tag = unsafe { self.ctrl.as_ptr().add(index).read() };

            if unlikely(tag.is_full()) {
                debug_assert!(self.bucket_mask < Group::WIDTH);

                // SAFETY:
                //
                // * Since the caller of this function ensures that the control bytes are properly
                //   initialized and `ptr = self.ctrl(0)` points to the start of the array of control
                //   bytes, therefore: `ctrl` is valid for reads, properly aligned to `Group::WIDTH`
                //   and points to the properly initialized control bytes (see also
                //   `TableLayout::calculate_layout_for` and `ptr::read`);
                //
                // * Because the caller of this function ensures that the index was provided by the
                //   `self.find_insert_slot_in_group()` function, so for for tables larger than the
                //   group width (self.buckets() >= Group::WIDTH), we will never end up in the given
                //   branch, since `(probe_seq.pos + bit) & self.bucket_mask` in `find_insert_slot_in_group`
                //   cannot return a full bucket index. For tables smaller than the group width, calling
                //   the `unwrap_unchecked` function is also safe, as the trailing control bytes outside
                //   the range of the table are filled with EMPTY bytes (and we know for sure that there
                //   is at least one FULL bucket), so this second scan either finds an empty slot (due to
                //   the load factor) or hits the trailing control bytes (containing EMPTY).
                index = unsafe {
                    Group::load_aligned(self.ctrl.as_ptr())
                        .match_empty_or_deleted()
                        .lowest_set_bit()
                        .unwrap_unchecked()
                };
            }
            Some(index)
        } else {
            None
        }
    }

    /// Give the indices and items associated with the full buckets in this group.
    ///
    /// # Safety
    ///
    /// The type of the items must be correct for the table.
    pub(crate) unsafe fn full<T>(&self) -> GroupProbeItems<T> {
        GroupProbeItems {
            ctrl: self.ctrl,
            iter: self.group.match_tag(self.hash_tag).into_iter(),
            index: self.index,
            bucket_mask: self.bucket_mask,
            marker: PhantomData,
        }
    }

    /// Finds the index of an item.
    ///
    /// # Safety
    ///
    /// The type of the items must be correct for the table.
    pub(crate) unsafe fn find_full<T>(&self, f: impl FnMut(&T) -> bool) -> Option<usize> {
        self.full().find(f)
    }

    /// Finds the index of an item, or a spot to insert it.
    ///
    /// # Safety
    ///
    /// The type of the items must be correct for the table.
    pub(crate) unsafe fn find_full_or_empty<T>(
        &self,
        f: impl FnMut(&T) -> bool,
    ) -> Result<usize, Option<usize>> {
        if let Some(index) = self.full().find(f) {
            Ok(index)
        } else {
            Err(self.empty())
        }
    }
}

/// Actual items in a group.
///
/// Returned by [`GroupProbe::full`].
pub(crate) struct GroupProbeItems<T> {
    /// Original control pointer.
    ctrl: NonNull<Tag>,

    /// Iterator over full buckets in the group.
    iter: BitMaskIter,

    /// Index of the group.
    index: usize,

    /// Number of buckets, minus one.
    bucket_mask: usize,

    /// Marker indicating that we have items of type T.
    marker: PhantomData<*const T>,
}
impl<T> GroupProbeItems<T> {
    /// Return the index of the first item that satisfies the predicate.
    pub(crate) fn find(self, mut f: impl FnMut(&T) -> bool) -> Option<usize> {
        for (index, item) in self {
            // SAFETY: The item lives long enough for the function to check it.
            if likely(f(unsafe { &*item.as_ptr() })) {
                return Some(index);
            }
        }
        None
    }
}
impl<T> Clone for GroupProbeItems<T> {
    fn clone(&self) -> Self {
        GroupProbeItems {
            ctrl: self.ctrl,
            iter: self.iter.clone(),
            index: self.index,
            bucket_mask: self.bucket_mask,
            marker: PhantomData,
        }
    }
}
impl<T> Iterator for GroupProbeItems<T> {
    type Item = (usize, NonNull<T>);
    fn next(&mut self) -> Option<(usize, NonNull<T>)> {
        // SAFETY: We uphold our own constraints, and this function was made for us.
        Some(unsafe {
            group_probe_items(self.ctrl, self.index, self.iter.next()?, self.bucket_mask)
        })
    }
}

/// Common functionality for [`GroupProbeItems`] and [`ProbeItems`].
///
/// # Safety
///
/// Must satisfy the constraints of [`GroupProbeItems`].
unsafe fn group_probe_items<T>(
    ctrl: NonNull<Tag>,
    index: usize,
    bit: usize,
    bucket_mask: usize,
) -> (usize, NonNull<T>) {
    let index = (index + bit) & bucket_mask;

    // SAFETY: Because the hash table is valid, we expect that a matching
    //   full tag will have an initialized item in the table. Because we
    //   mask with the bucket mask, we know that the index is in-bounds and
    //   refers to the actual initialized item.
    let item = unsafe { ctrl.cast::<T>().as_ptr().sub(1 + index) };

    // FIXME: Once MSRV > 1.80.0, we can use `NonNull::sub`.
    // SAFETY: Since our pointer is in bounds, it's non-null.
    let item = unsafe { NonNull::new_unchecked(item) };

    (index, item)
}

/// Flat-map of [`Probe`] into [`GroupProbeItems`], but with deduped fields.
pub(crate) struct ProbeItems<T> {
    /// Probe.
    probe: Probe,

    /// Index of currently matched group.
    index: usize,

    /// Iterator over full buckets in the group.
    iter: BitMaskIter,

    /// Marker indicating that we have items of type T.
    marker: PhantomData<*const T>,
}
impl<T> Clone for ProbeItems<T> {
    fn clone(&self) -> Self {
        ProbeItems {
            probe: self.probe.clone(),
            iter: self.iter.clone(),
            index: self.index,
            marker: PhantomData,
        }
    }
}
impl<T> Iterator for ProbeItems<T> {
    type Item = (usize, NonNull<T>);

    fn next(&mut self) -> Option<(usize, NonNull<T>)> {
        loop {
            if let Some(bit) = self.iter.next() {
                // SAFETY: This function was made for us, and we uphold our own constraints.
                return Some(unsafe {
                    group_probe_items(self.probe.ctrl, self.index, bit, self.probe.bucket_mask)
                });
            } else if self.probe.current().has_empty() {
                return None;
            } else {
                // SAFETY: The probe always returns an item.
                let group_probe = unsafe { self.probe.next().unwrap_unchecked() };

                // SAFETY: The hash table contains this type of items.
                let full = unsafe { group_probe.full::<T>() };
                self.iter = full.iter;
                self.index = full.index;
            }
        }
    }
}

/// Probe which iterates through groups in the control data to search for
/// buckets for a given hash value.
///
/// Sequence based on triangular numbers, which is guaranteed (since our table
/// size is a power of two) to visit every group of elements exactly once.
///
/// A triangular probe has us jump by 1 more group every time. So first we
/// jump by 1 group (meaning we just continue our linear scan), then 2 groups
/// (skipping over 1 group), then 3 groups (skipping over 2 groups), and so on.
///
/// Proof that the probe will visit every group in the table:
/// <https://fgiesen.wordpress.com/2015/02/22/triangular-numbers-mod-2n/>
#[derive(Clone)]
pub(crate) struct Probe {
    /// Current position in sequence.
    pos: usize,

    /// Offset from current position to next group.
    stride: usize,

    /// Pointer to control data.
    ctrl: NonNull<Tag>,

    /// Number of buckets, minus one.
    bucket_mask: usize,

    /// Tag containing the hash of the item.
    hash_tag: Tag,

    /// Initial hash, for debugging.
    #[cfg(debug_assertions)]
    hash: u64,

    /// Current iteration, for debugging.
    #[cfg(debug_assertions)]
    iter: usize,
}
impl Probe {
    /// Creates a new probe for a table for a given hash.
    ///
    /// # Safety
    ///
    /// The given bucket mask must be equal to the power-of-two number of buckets minus one,
    /// and the given control pointer must be a valid hash table.
    pub(crate) unsafe fn new(ctrl: NonNull<Tag>, bucket_mask: usize, hash: u64) -> Probe {
        debug_assert!((bucket_mask + 1).is_power_of_two());

        Probe {
            // On 32-bit platforms we simply ignore the higher hash bits.
            //
            // We need to apply the bucket mask now in the rare case where it
            // would fall greater than `usize::MAX - Group::WIDTH`, since it
            // could overflow.
            pos: (hash as usize) & bucket_mask,
            hash_tag: Tag::full(hash),
            stride: 0,
            ctrl,
            bucket_mask,
            #[cfg(debug_assertions)]
            hash,
            #[cfg(debug_assertions)]
            iter: 0,
        }
    }

    /// Gets the inner slice of groups.
    fn control_slice(&self) -> &[Tag] {
        // SAFETY: We always allocate this many control tags.
        unsafe { slice::from_raw_parts(self.ctrl.as_ptr(), self.bucket_mask + 1 + Group::WIDTH) }
    }

    /// Verifies that the control slice is valid.
    fn assert_at_least_one_empty(&self) {
        let control = self.control_slice();
        debug_assert!(
            control.iter().any(|tag| tag.is_empty()),
            "control slice was completely full: {:x?}",
            control
        );
    }

    /// Finds an empty slot to insert something.
    ///
    /// Although not a safety violation, this method *will* loop infinitely if
    /// the table does not contain an empty slot. You have been warned.
    pub(crate) fn empty(mut self) -> usize {
        self.assert_at_least_one_empty();
        loop {
            // SAFETY: We always return an item from the iterator.
            let group_probe = unsafe { self.next().unwrap_unchecked() };

            let empty = group_probe.empty();
            if likely(empty.is_some()) {
                // SAFETY: We have some.
                return unsafe { empty.unwrap_unchecked() };
            }
        }
    }

    /// Iterates over the full slots.
    ///
    /// Effectively `flat_map(Group::full)`, but with deduped fields.
    ///
    /// # Safety
    ///
    /// The hash table must contain the given type of items.
    pub(crate) fn full<T>(mut self) -> ProbeItems<T> {
        // SAFETY: We always return an item from the iterator.
        let group_probe = unsafe { self.next().unwrap_unchecked() };

        // SAFETY: The caller ensures the hash table contains this type of items.
        let full = unsafe { group_probe.full::<T>() };
        ProbeItems {
            probe: self,
            index: full.index,
            iter: full.iter,
            marker: PhantomData,
        }
    }

    /// Finds a full slot.
    ///
    /// Although not a safety violation, this method *will* loop infinitely if
    /// the table does not contain an empty slot. You have been warned.
    ///
    /// # Safety
    ///
    /// The hash table must contain the given type of items.
    pub(crate) fn find_full<T>(mut self, mut f: impl FnMut(&T) -> bool) -> Option<usize> {
        self.assert_at_least_one_empty();
        loop {
            // SAFETY: We always return an item from the iterator.
            let group_probe = unsafe { self.next().unwrap_unchecked() };

            // SAFETY: The caller ensures the table contains the given type of items.
            match unsafe { group_probe.find_full(&mut f) } {
                Some(index) => return Some(index),
                None => {
                    if group_probe.has_empty() {
                        return None;
                    }
                }
            }
        }
    }

    /// Finds a full slot or an empty slot to insert something.
    ///
    /// Although not a safety violation, this method *will* loop infinitely if
    /// the table does not contain an empty slot. You have been warned.
    ///
    /// # Safety
    ///
    /// The hash table must contain the given type of items.
    pub(crate) fn find_full_or_empty<T>(
        mut self,
        mut f: impl FnMut(&T) -> bool,
    ) -> Result<usize, usize> {
        self.assert_at_least_one_empty();
        loop {
            // SAFETY: We always return an item from the iterator.
            let group_probe = unsafe { self.next().unwrap_unchecked() };

            // SAFETY: The caller ensures the table contains the given type of items.
            match unsafe { group_probe.find_full_or_empty(&mut f) } {
                Ok(index) => return Ok(index),
                Err(Some(index)) => return Err(index),
                Err(None) => (),
            }
        }
    }

    /// Gets the previously yielded group probe.
    fn current(&self) -> GroupProbe {
        // SAFETY: We ensure that we have num_buckets + Group::WIDTH tags in the control,
        //   so that this is always in-bounds. We also pass along the guarantees that this
        //   is a valid hash table, and since we made the tag with `Tag::full`, we also
        //   know that it is a full tag.
        let group = unsafe { Group::load(self.ctrl.as_ptr().add(self.pos)) };
        GroupProbe {
            ctrl: self.ctrl,
            hash_tag: self.hash_tag,
            group,
            bucket_mask: self.bucket_mask,
            index: self.pos,
        }
    }
}
impl Iterator for Probe {
    type Item = GroupProbe;
    fn next(&mut self) -> Option<GroupProbe> {
        #[cfg(debug_assertions)]
        {
            if self.iter > self.bucket_mask {
                // We should have found an empty bucket by now and ended the probe.
                panic!(
                    "Went past end of probe sequence searching for hash {:x?} (tag {:x?}, index {:?}) in {:x?}",
                    self.hash,
                    self.hash_tag,
                    (self.hash as usize & self.bucket_mask),
                    self.control_slice()
                );
            }
            self.iter += 1;
        }

        self.stride += Group::WIDTH;
        self.pos += self.stride;
        self.pos &= self.bucket_mask;

        Some(self.current())
    }
}
