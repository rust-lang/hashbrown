use super::group::{BITMASK_ITER_MASK, BITMASK_STRIDE, BitMaskWord, NonZeroBitMaskWord};

/// A bit mask which contains the result of a `Match` operation on a `Group` and
/// allows iterating through them.
///
/// The bit mask is arranged so that low-order bits represent lower memory
/// addresses for group match results.
///
/// For implementation reasons, the bits in the set may be sparsely packed with
/// groups of 8 bits representing one element. If any of these bits are non-zero
/// then this element is considered to true in the mask. If this is the
/// case, `BITMASK_STRIDE` will be 8 to indicate a divide-by-8 should be
/// performed on counts/indices to normalize this difference. `BITMASK_MASK` is
/// similarly a mask of all the actually-used bits.
///
/// To iterate over a bit mask, it must be converted to a form where only 1 bit
/// is set per element. This is done by applying `BITMASK_ITER_MASK` on the
/// mask bits.
#[derive(Copy, Clone)]
pub(crate) struct BitMask(pub(crate) BitMaskWord);

#[expect(clippy::use_self)]
impl BitMask {
    /// A BitMask only requires each element (group of bits) to be non-zero.
    /// However for iteration we need each element to only contain 1 bit.
    ///
    /// On some SIMD backends (notably ARM NEON), a single logical match may occupy
    /// multiple raw bits, so manual iteration must normalize the mask first.
    ///
    /// # Warning
    /// Call this before manually iterating with `lowest_set_bit` and
    /// `remove_lowest_bit`.
    #[inline]
    #[must_use]
    pub(crate) fn normalize_for_iteration(self) -> Self {
        BitMask(self.0 & BITMASK_ITER_MASK)
    }

    /// Returns a new `BitMask` with the lowest bit removed.
    ///
    /// # Warning
    /// If you are using this in a loop to iterate over matches, you **must**
    /// call [`BitMask::normalize_for_iteration`] on the mask first.
    #[inline]
    #[must_use]
    pub(crate) fn remove_lowest_bit(self) -> Self {
        BitMask(self.0 & (self.0 - 1))
    }

    /// Returns whether the `BitMask` has at least one set bit.
    #[inline]
    pub(crate) fn any_bit_set(self) -> bool {
        self.0 != 0
    }

    /// Returns the first set bit in the `BitMask`, if there is one.
    ///
    /// # Warning
    /// If you are using this in a loop to iterate over matches, you **must**
    /// call [`BitMask::normalize_for_iteration`] on the mask first.
    #[inline]
    pub(crate) fn lowest_set_bit(self) -> Option<usize> {
        if let Some(nonzero) = NonZeroBitMaskWord::new(self.0) {
            Some(Self::nonzero_trailing_zeros(nonzero))
        } else {
            None
        }
    }

    /// Returns the number of trailing zeroes in the `BitMask`.
    #[inline]
    pub(crate) fn trailing_zeros(self) -> usize {
        // ARM doesn't have a trailing_zeroes instruction, and instead uses
        // reverse_bits (RBIT) + leading_zeroes (CLZ). However older ARM
        // versions (pre-ARMv7) don't have RBIT and need to emulate it
        // instead. Since we only have 1 bit set in each byte on ARM, we can
        // use swap_bytes (REV) + leading_zeroes instead.
        if cfg!(target_arch = "arm") && BITMASK_STRIDE % 8 == 0 {
            self.0.swap_bytes().leading_zeros() as usize / BITMASK_STRIDE
        } else {
            self.0.trailing_zeros() as usize / BITMASK_STRIDE
        }
    }

    /// Same as above but takes a `NonZeroBitMaskWord`.
    #[inline]
    fn nonzero_trailing_zeros(nonzero: NonZeroBitMaskWord) -> usize {
        if cfg!(target_arch = "arm") && BITMASK_STRIDE % 8 == 0 {
            // SAFETY: A byte-swapped non-zero value is still non-zero.
            let swapped = unsafe { NonZeroBitMaskWord::new_unchecked(nonzero.get().swap_bytes()) };
            swapped.leading_zeros() as usize / BITMASK_STRIDE
        } else {
            nonzero.trailing_zeros() as usize / BITMASK_STRIDE
        }
    }

    /// Returns the number of leading zeroes in the `BitMask`.
    #[inline]
    pub(crate) fn leading_zeros(self) -> usize {
        self.0.leading_zeros() as usize / BITMASK_STRIDE
    }
}

impl IntoIterator for BitMask {
    type Item = usize;
    type IntoIter = BitMaskIter;

    #[inline]
    fn into_iter(self) -> BitMaskIter {
        BitMaskIter(self.normalize_for_iteration())
    }
}

/// Iterator over the contents of a `BitMask`, returning the indices of set
/// bits.
#[derive(Clone)]
pub(crate) struct BitMaskIter(pub(crate) BitMask);

impl Iterator for BitMaskIter {
    type Item = usize;

    #[inline]
    fn next(&mut self) -> Option<usize> {
        let bit = self.0.lowest_set_bit()?;
        self.0 = self.0.remove_lowest_bit();
        Some(bit)
    }
}

#[cfg(test)]
mod tests {
    use crate::control::{Group, Tag};
    use stdalloc::vec::Vec;

    #[test]
    fn match_tag_iteration_yields_expected_positions() {
        let tag = Tag::full(0);
        let positions = [1, Group::WIDTH / 2, Group::WIDTH - 1];

        let mut ctrl = [Tag::EMPTY; Group::WIDTH];
        for i in positions {
            ctrl[i] = tag;
        }

        let got = unsafe { Group::load(ctrl.as_ptr().cast()) }
            .match_tag(tag)
            .into_iter()
            .collect::<Vec<_>>();

        assert_eq!(got.as_slice(), &positions);
    }

    #[test]
    fn normalized_manual_drain_yields_expected_positions() {
        let tag = Tag::full(0);
        let positions = [1, Group::WIDTH / 2, Group::WIDTH - 1];

        let mut ctrl = [Tag::EMPTY; Group::WIDTH];
        for i in positions {
            ctrl[i] = tag;
        }

        let mut mask = unsafe { Group::load(ctrl.as_ptr().cast()) }
            .match_tag(tag)
            .normalize_for_iteration();

        let mut got = Vec::new();
        while let Some(bit) = mask.lowest_set_bit() {
            got.push(bit);
            mask = mask.remove_lowest_bit();
        }

        assert_eq!(got.as_slice(), &positions);
    }
}
