// FIXME: Use `core::hint::{likely, unlikely, cold_path}` unconditionally once the MSRV supports them.
#[cfg(feature = "nightly")]
pub(crate) use core::intrinsics::{cold_path, likely, unlikely};

/// Hints to the compiler that the code path calling this function is cold
/// (unlikely to be executed).
#[cfg(not(feature = "nightly"))]
#[inline(always)]
#[cold]
pub(crate) fn cold_path() {}

#[cfg(not(feature = "nightly"))]
#[inline(always)]
pub(crate) fn likely(b: bool) -> bool {
    if b {
        true
    } else {
        cold_path();
        false
    }
}

#[cfg(not(feature = "nightly"))]
#[inline(always)]
pub(crate) fn unlikely(b: bool) -> bool {
    if b {
        cold_path();
        true
    } else {
        false
    }
}
