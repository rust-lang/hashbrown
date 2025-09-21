use core::{fmt, mem};

/// Single tag in a control group.
#[derive(Copy, Clone, PartialEq, Eq)]
#[repr(transparent)]
pub(crate) struct Tag(pub(super) i8);
impl Tag {
    /// Control tag value for an empty bucket.
    pub(crate) const EMPTY: Tag = Tag(0b0111_1111); // 127
    pub(crate) const EMPTY32: i32 = 0x7F7F7F7F;

    /// Control tag value for a deleted bucket.
    pub(crate) const DELETED: Tag = Tag(0b0111_1110); // 126
    pub(crate) const DELETED32: i32 = 0x7E7E7E7E;

    pub(crate) const MAX_TAG32: i32 = 0x7D7D7D7D; // 4*125

    /// Checks whether a control tag represents a full bucket (top bit is clear).
    #[inline]
    pub(crate) const fn is_full(self) -> bool {
        self.0 < Tag::DELETED.0
    }

    /// Checks whether a control tag represents a special value (top bit is set).
    #[inline]
    pub(crate) const fn is_special(self) -> bool {
        self.0 >= Tag::DELETED.0
    }

    /// Checks whether a special control value is EMPTY (just check 1 bit).
    #[inline]
    pub(crate) const fn special_is_empty(self) -> bool {
        debug_assert!(self.is_special());
        self.0 == Tag::EMPTY.0
    }

    /// Creates a control tag representing a full bucket with the given hash.
    #[inline(always)]
    #[allow(clippy::cast_possible_truncation)]
    pub(crate) const fn full(hash: u64) -> Tag {
        Tag(Self::full32(hash) as i8)
    }
    
    #[inline]
    #[allow(clippy::cast_possible_truncation)]
    pub(crate) const fn full32(hash: u64) -> i32 {
        // Constant for function that grabs the top 8 bits * 4 of the hash.
        const MIN_HASH_LEN: usize = if mem::size_of::<usize>() < mem::size_of::<u64>() {
            mem::size_of::<usize>()
        } else {
            mem::size_of::<u64>()
        };

        // Constant array of 8 bits duplicated as 32 bits
        // with re-mapping of special values.
        const fn compute_control() -> [i32; 256] {
            let mut result = [0; 256];

            let mut i: u32 = 0;
            while i < 256 {
                result[i as usize] = (i | (i << 8) | (i << 16) | (i << 24)) as i32;
                i += 1;
            }

            // Avoid overlap with special values.
            result[Tag::EMPTY.0 as usize] = 0x29292929;
            result[Tag::DELETED.0 as usize] = 0x53535353;

            result
        }
        const CONTROL: [i32; 256] = compute_control();
        
        // Grab the top 8 bits of the hash. While the hash is normally a full 64-bit
        // value, some hash functions (such as FxHash) produce a usize result
        // instead, which means that the top 32 bits are 0 on 32-bit platforms.
        // So we use MIN_HASH_LEN constant to handle this.
        let top8 = (hash >> (MIN_HASH_LEN * 8 - 8)) as usize;
        CONTROL[top8] // truncation
    }
}
impl fmt::Debug for Tag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_special() {
            if self.special_is_empty() {
                f.pad("EMPTY")
            } else {
                f.pad("DELETED")
            }
        } else {
            f.debug_tuple("full").field(&self.0).finish()
        }
    }
}

/// Extension trait for slices of tags.
pub(crate) trait TagSliceExt {
    /// Fills the control with the given tag.
    fn fill_tag(&mut self, tag: Tag);

    /// Clears out the control.
    #[inline]
    fn fill_empty(&mut self) {
        self.fill_tag(Tag::EMPTY)
    }
}
impl TagSliceExt for [Tag] {
    #[inline]
    fn fill_tag(&mut self, tag: Tag) {
        // SAFETY: We have access to the entire slice, so, we can write to the entire slice.
        unsafe { self.as_mut_ptr().write_bytes(tag.0 as u8, self.len()) }
    }
}
