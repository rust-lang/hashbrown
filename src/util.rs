// FIXME: Replace with `core::hint::{likely, unlikely}` once they are stable.
#[cfg(feature = "nightly")]
pub(crate) use core::intrinsics::{likely, unlikely};

#[cfg(not(feature = "nightly"))]
use core::hint::cold_path;

#[cfg(not(feature = "nightly"))]
#[inline(always)]
pub const fn likely(b: bool) -> bool {
    if !b {
        cold_path();
    }
    b
}

#[cfg(not(feature = "nightly"))]
#[inline(always)]
pub const fn unlikely(b: bool) -> bool {
    if b {
        cold_path();
    }
    b
}

// FIXME: use strict provenance functions once they are stable.
// Implement it with a transmute for now.
#[inline(always)]
pub(crate) fn invalid_mut<T>(addr: usize) -> *mut T {
    unsafe { core::mem::transmute(addr) }
}
