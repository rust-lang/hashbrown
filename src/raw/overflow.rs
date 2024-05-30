//! Overflow tracking, for finer grained probing.
//!
//! This modules defines an `OverflowTracker`, selected by features.
//!
//! An `OverflowTracker` tracks, in some fashion, whether elements inserted into the hash-table overflowed the group
//! paired with the `OverflowTracker`. During a look-up, the `OverflowTracker` can then indicate whether further probing
//! is necessary or not, though on a probalistic basis: it can indicate "no" with certainty, but only a "maybe"
//! otherwise.
//!
//! Which `OverflowTracker` to choose is... a good question.
//!
//! Elements to consider:
//!
//! -   No overflow: no tracker! If insertion never overflows nor fully fills a group, then any overflow tracking is
//!     pure overhead.
//! -   No removal: no counter! If the hash-table is append-only, then counters (which allow clean-up on removal) are
//!     pure overhead.
//! -   Bloom is good! Bloom-filter based trackers are expected to perform better than pure-counter trackers.

pub use imp::OverflowTracker;

#[cfg(not(any(
    feature = "overflow-tracker-counter-u8",
    feature = "overflow-tracker-bloom-1-u8",
    feature = "overflow-tracker-bloom-1-u16",
    feature = "overflow-tracker-hybrid"
)))]
mod imp {
    /// An intangible `OverflowTracker` which tracks nothing.
    pub struct OverflowTracker(());

    impl OverflowTracker {
        /// Does not track removals.
        ///
        /// The `remove` function will unconditionally panic, it is only provided to ease compilation.
        pub const TRACK_REMOVALS: bool = false;

        /// Adds the `h2` to the tracker.
        #[inline(always)]
        pub fn add(&mut self, _h2: u8) {}

        /// Removes the `h2` from the tracker, if supported.
        #[inline(always)]
        pub fn remove(&mut self, _h2: u8) {
            unreachable!("`remove` should not be called when `TRACK_REMOVALS` is false");
        }

        /// Returns whether the element of this `h2` may be further ahead in the probing sequence, or not.
        ///
        /// This is a probalistic response. `false` is definite, `true` is only a possibility.
        #[inline(always)]
        pub fn may_have_overflowed(&self, _h2: u8) -> bool {
            true
        }
    }
} // mod imp

#[cfg(feature = "overflow-tracker-counter-u8")]
mod imp {
    /// A counter based `OverflowTracker`.
    ///
    /// The counter tracks the number of elements which overflowed, and were not yet removed. If a great number of
    /// elements overflow, the counter saturates, and removal is no longer tracked.
    ///
    /// This strategy is used in Facebook's F14 hash-table.
    pub struct OverflowTracker(u8);

    impl OverflowTracker {
        /// Tracks removal in a best-effort fashion.
        ///
        /// If the tracker overflows, removals can no longer be tracked, and calling `remove` has no effect.
        pub const TRACK_REMOVALS: bool = true;

        /// Adds the `h2` to the tracker.
        #[inline(always)]
        pub fn add(&mut self, _h2: u8) {
            self.0 = self.0.saturating_add(1);
        }

        /// Removes the `h2` from the tracker, if supported.
        #[inline(always)]
        pub fn remove(&mut self, _h2: u8) {
            //  The counter is saturated, an unknown number of additions may have been ignored, and thus removals can no
            //  longer be tracked.
            if self.0 == u8::MAX {
                return;
            }

            self.0 -= 1;
        }

        /// Returns whether the element of this `h2` may be further ahead in the probing sequence, or not.
        ///
        /// This is a probalistic response. `false` is definite, `true` is only a possibility.
        #[inline(always)]
        pub fn may_have_overflowed(&self, _h2: u8) -> bool {
            self.0 > 0
        }
    }
} // mod imp

#[cfg(feature = "overflow-tracker-bloom-1-u8")]
mod imp {
    /// A bloom-filter based `OverflowTracker`.
    ///
    /// The filter tracks whether an element with the same "reduced" hash has ever overflowed. It cannot distinguish
    /// between different elements with the same "reduced" hash, and thus cannot track removals.
    ///
    /// This strategy is used in Boost's `std::unordered_flat_map`.
    pub struct OverflowTracker(u8);

    impl OverflowTracker {
        /// Does not track removals.
        ///
        /// The `remove` function will unconditionally panic, it is only provided to ease compilation.
        pub const TRACK_REMOVALS: bool = false;

        /// Adds the `h2` to the tracker.
        #[inline(always)]
        pub fn add(&mut self, h2: u8) {
            self.0 |= Self::mask(h2);
        }

        /// Removes the `h2` from the tracker, if supported.
        #[inline(always)]
        pub fn remove(&mut self, _h2: u8) {
            unreachable!("`remove` should not be called when `TRACK_REMOVALS` is false");
        }

        /// Returns whether the element of this `h2` may be further ahead in the probing sequence, or not.
        ///
        /// This is a probalistic response. `false` is definite, `true` is only a possibility.
        #[inline(always)]
        pub fn may_have_overflowed(&self, h2: u8) -> bool {
            (self.0 & Self::mask(h2)) != 0
        }

        #[inline(always)]
        fn mask(h2: u8) -> u8 {
            1u8 << (h2 & 0x7)
        }
    }
} // mod imp

#[cfg(feature = "overflow-tracker-bloom-1-u16")]
mod imp {
    /// A bloom-filter based `OverflowTracker`.
    ///
    /// The filter tracks whether an element with the same "reduced" hash has ever overflowed. It cannot distinguish
    /// between different elements with the same "reduced" hash, and thus cannot track removals.
    ///
    /// This tracker uses twice as many bits as Boost's `std::unordered_map` in an attempt to improve accuracy.
    pub struct OverflowTracker(u16);

    impl OverflowTracker {
        /// Does not track removals.
        ///
        /// The `remove` function will unconditionally panic, it is only provided to ease compilation.
        pub const TRACK_REMOVALS: bool = false;

        /// Adds the `h2` to the tracker.
        #[inline(always)]
        pub fn add(&mut self, h2: u8) {
            self.0 |= Self::mask(h2);
        }

        /// Removes the `h2` from the tracker, if supported.
        #[inline(always)]
        pub fn remove(&mut self, _h2: u8) {
            unreachable!("`remove` should not be called when `TRACK_REMOVALS` is false");
        }

        /// Returns whether the element of this `h2` may be further ahead in the probing sequence, or not.
        ///
        /// This is a probalistic response. `false` is definite, `true` is only a possibility.
        #[inline(always)]
        pub fn may_have_overflowed(&self, h2: u8) -> bool {
            (self.0 & Self::mask(h2)) != 0
        }

        #[inline(always)]
        fn mask(h2: u8) -> u16 {
            1u16 << (h2 & 0xF)
        }
    }
} // mod imp

#[cfg(feature = "overflow-tracker-hybrid")]
mod imp {
    /// A hybrid counter and bloom-filter based `OverflowTracker`.
    ///
    /// This combines both a counter and a filter. This allows tracking removals coarsely, while also tracking elements
    /// in a more fine-grained fashion than with a pure counter.
    pub struct OverflowTracker {
        counter: u8,
        filter: u8,
    }

    impl OverflowTracker {
        /// Tracks removal in a best-effort fashion.
        ///
        /// If the tracker overflows, removals can no longer be tracked, and calling `remove` has no effect.
        pub const TRACK_REMOVALS: bool = true;

        /// Adds the `h2` to the tracker.
        #[inline(always)]
        pub fn add(&mut self, h2: u8) {
            self.counter = self.counter.saturating_add(1);
            self.filter |= Self::mask(h2);
        }

        /// Removes the `h2` from the tracker, if supported.
        #[inline(always)]
        pub fn remove(&mut self, _h2: u8) {
            //  The counter is saturated, an unknown number of additions may have been ignored, and thus removals can no
            //  longer be tracked.
            if self.counter == u8::MAX {
                return;
            }

            self.counter -= 1;

            if self.counter == 0 {
                self.filter = 0;
            }
        }

        /// Returns whether the element of this `h2` may be further ahead in the probing sequence, or not.
        ///
        /// This is a probalistic response. `false` is definite, `true` is only a possibility.
        #[inline(always)]
        pub fn may_have_overflowed(&self, h2: u8) -> bool {
            (self.filter & Self::mask(h2)) != 0
        }

        #[inline(always)]
        fn mask(h2: u8) -> u8 {
            1u8 << (h2 & 0x7)
        }
    }
} // mod imp
