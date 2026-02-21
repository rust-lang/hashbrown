use super::super::{BitMask, Tag};
use core::mem;
use core::num::NonZeroU16;

use core::arch::wasm32;

pub(crate) type BitMaskWord = u16;
pub(crate) type NonZeroBitMaskWord = NonZeroU16;
pub(crate) const BITMASK_STRIDE: usize = 1;
pub(crate) const BITMASK_ITER_MASK: BitMaskWord = !0;

/// Abstraction over a group of control tags which can be scanned in
/// parallel.
///
/// This implementation uses a v128 value.
#[derive(Copy, Clone)]
pub(crate) struct Group(wasm32::v128);

// FIXME: https://github.com/rust-lang/rust-clippy/issues/3859
#[expect(clippy::use_self)]
impl Group {
    /// Number of bytes in the group.
    pub(crate) const WIDTH: usize = mem::size_of::<Self>();

    /// Returns a full group of empty tags, suitable for use as the initial
    /// value for an empty hash table.
    ///
    /// This is guaranteed to be aligned to the group size.
    #[inline]
    pub(crate) const fn static_empty() -> &'static [Tag; Group::WIDTH] {
        #[repr(C)]
        struct AlignedTags {
            _align: [Group; 0],
            tags: [Tag; Group::WIDTH],
        }
        const ALIGNED_TAGS: AlignedTags = AlignedTags {
            _align: [],
            tags: [Tag::EMPTY; Group::WIDTH],
        };
        &ALIGNED_TAGS.tags
    }

    /// Loads a group of tags starting at the given address.
    #[inline]
    pub(crate) unsafe fn load(ptr: *const Tag) -> Self {
        unsafe { Group(wasm32::v128_load(ptr.cast())) }
    }

    /// Loads a group of tags starting at the given address, which must be
    /// aligned to `mem::align_of::<Group>()`.
    #[inline]
    pub(crate) unsafe fn load_aligned(ptr: *const Tag) -> Self {
        debug_assert_eq!(ptr.align_offset(mem::align_of::<Self>()), 0);
        unsafe { Group(wasm32::v128_load(ptr.cast())) }
    }

    /// Stores the group of tags to the given address, which must be
    /// aligned to `mem::align_of::<Group>()`.
    #[inline]
    pub(crate) unsafe fn store_aligned(self, ptr: *mut Tag) {
        debug_assert_eq!(ptr.align_offset(mem::align_of::<Self>()), 0);
        unsafe {
            wasm32::v128_store(ptr.cast(), self.0);
        }
    }

    /// Returns a `BitMask` indicating all tags in the group which have
    /// the given value.
    #[inline]
    pub(crate) fn match_tag(self, tag: Tag) -> BitMask {
        let cmp = wasm32::i8x16_eq(self.0, wasm32::i8x16_splat(tag.0 as i8));
        BitMask(wasm32::i8x16_bitmask(cmp))
    }

    /// Returns a `BitMask` indicating all tags in the group which are
    /// `EMPTY`.
    #[inline]
    pub(crate) fn match_empty(self) -> BitMask {
        self.match_tag(Tag::EMPTY)
    }

    /// Returns a `BitMask` indicating all tags in the group which are
    /// `EMPTY` or `DELETED`.
    #[inline]
    pub(crate) fn match_empty_or_deleted(self) -> BitMask {
        // A tag is EMPTY or DELETED iff the high bit is set
        BitMask(wasm32::i8x16_bitmask(self.0))
    }

    /// Returns a `BitMask` indicating all tags in the group which are full.
    #[inline]
    pub(crate) fn match_full(&self) -> BitMask {
        BitMask(!self.match_empty_or_deleted().0)
    }

    /// Performs the following transformation on all tags in the group:
    /// - `EMPTY => EMPTY`
    /// - `DELETED => EMPTY`
    /// - `FULL => DELETED`
    #[inline]
    pub(crate) fn convert_special_to_empty_and_full_to_deleted(self) -> Self {
        // Map high_bit = 1 (EMPTY or DELETED) to 1111_1111
        // and high_bit = 0 (FULL) to 1000_0000
        //
        // Here's this logic expanded to concrete values:
        //   let special = 0 > tag = 1111_1111 (true) or 0000_0000 (false)
        //   1111_1111 | 1000_0000 = 1111_1111
        //   0000_0000 | 1000_0000 = 1000_0000
        let zero = wasm32::i8x16_splat(0);
        let special = wasm32::i8x16_gt(zero, self.0);
        Group(wasm32::v128_or(
            special,
            wasm32::i8x16_splat(Tag::DELETED.0 as i8),
        ))
    }
}
