//! Software prefetch hint.
//!
//! A prefetch is a *hint* to the CPU that the cache line containing a given
//! address will be accessed soon, so the memory subsystem can start fetching it
//! while the core does other work. It is purely advisory: it never reads or
//! writes memory, never faults (even for an invalid or dangling pointer), and is
//! a no-op in the Rust abstract machine. Architectures without a stable prefetch
//! intrinsic simply compile it away.
//!
//! `core::intrinsics::prefetch_read_data` is unstable, so we cannot use it here.
//! Instead we use the stable per-architecture intrinsics where they exist
//! (`_mm_prefetch` on x86/x86-64) and fall back to a no-op everywhere else.

/// Issues an L1 read prefetch for the cache line containing `ptr`.
///
/// This is a hint only. `ptr` does not need to be valid, aligned, or even
/// non-null; an out-of-bounds or dangling pointer is fine and will not fault.
/// On targets without a stable prefetch intrinsic this is a no-op.
#[inline]
#[allow(clippy::let_unit_value)]
pub(crate) fn prefetch_read_l1(ptr: *const u8) {
    #[cfg(all(
        any(target_arch = "x86", target_arch = "x86_64"),
        target_feature = "sse",
        not(miri),
    ))]
    {
        #[cfg(target_arch = "x86")]
        use core::arch::x86::{_MM_HINT_T0, _mm_prefetch};
        #[cfg(target_arch = "x86_64")]
        use core::arch::x86_64::{_MM_HINT_T0, _mm_prefetch};

        // SAFETY: `_mm_prefetch` is a hint instruction; it performs no memory
        // access, never faults, and accepts any address (the Intel SDM and the
        // `core::arch` docs both spell this out). The only safety requirement is
        // that the `sse` target feature is available, which the `cfg` above
        // guarantees on x86 / x86-64.
        unsafe {
            _mm_prefetch::<_MM_HINT_T0>(ptr.cast::<i8>());
        }
    }

    #[cfg(not(all(
        any(target_arch = "x86", target_arch = "x86_64"),
        target_feature = "sse",
        not(miri),
    )))]
    {
        // No stable prefetch intrinsic on this target (aarch64 has none yet,
        // and `core::intrinsics::prefetch_read_data` is unstable). Make sure
        // `ptr` is still "used" so callers don't trip an unused-variable lint.
        let _ = ptr;
    }
}
