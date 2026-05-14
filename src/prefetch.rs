//! Software prefetch hint.
//!
//! A prefetch is a *hint* to the CPU that the cache line containing a given
//! address will be accessed soon, so the memory subsystem can start fetching it
//! while the core does other work. It is purely advisory: it never reads or
//! writes memory, never faults (even for an invalid or dangling pointer), and is
//! a no-op in the Rust abstract machine. Architectures without a stable prefetch
//! intrinsic simply compile it away.
//!
//! Two paths to the underlying hint:
//!
//! - **Stable shim (default).** Per-architecture stable intrinsics where they
//!   exist (`_mm_prefetch::<_MM_HINT_T0>` on x86/x86-64) and a no-op fallback
//!   elsewhere (aarch64 has no stable prefetch intrinsic).
//! - **Nightly intrinsic (`nightly` feature).** `core::intrinsics::prefetch_read_data::<_, 3>(ptr)`
//!   where locality `3` matches the stable shim's `_MM_HINT_T0` ("prefetch into
//!   all cache levels"). Available across all architectures the compiler
//!   recognizes. Gated on the `nightly` feature so end users can compare codegen
//!   against the stable shim on their target.

/// Issues an L1 read prefetch for the cache line containing `ptr`.
///
/// This is a hint only. `ptr` does not need to be valid, aligned, or even
/// non-null; an out-of-bounds or dangling pointer is fine and will not fault.
/// On targets without a stable prefetch intrinsic this is a no-op.
///
/// With the `nightly` feature enabled, this routes through
/// `core::intrinsics::prefetch_read_data::<_, 3>(ptr)`. Locality `3` is the
/// highest (all cache levels), matching the stable shim's `_MM_HINT_T0` on x86
/// so the two paths bench apples-to-apples.
#[inline]
#[allow(clippy::let_unit_value)]
pub(crate) fn prefetch_read_l1(ptr: *const u8) {
    #[cfg(feature = "nightly")]
    {
        // `prefetch_read_data` is safe to call: it performs no memory access,
        // never faults, and accepts any address. Locality `3` (const-generic
        // on the intrinsic) maps to the highest level (all caches), matching
        // `_MM_HINT_T0` on x86 so the comparison against the stable shim is
        // apples-to-apples.
        core::intrinsics::prefetch_read_data::<_, 3>(ptr);
    }

    #[cfg(all(
        not(feature = "nightly"),
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

    #[cfg(all(
        not(feature = "nightly"),
        not(all(
            any(target_arch = "x86", target_arch = "x86_64"),
            target_feature = "sse",
            not(miri),
        )),
    ))]
    {
        // No stable prefetch intrinsic on this target (aarch64 has none yet).
        // The `nightly` feature path covers it via `prefetch_read_data` when
        // available. Make sure `ptr` is still "used" so callers don't trip an
        // unused-variable lint.
        let _ = ptr;
    }
}
