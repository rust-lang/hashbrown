use std::sync::atomic::{self, AtomicUsize};

// Just an arbitrary side effect to make the maps not short circuit to the non-dropping path
// when dropping maps/entries (most real world usages likely have drop in the key or value)
lazy_static::lazy_static! {
    static ref SIDE_EFFECT: AtomicUsize = AtomicUsize::new(0);
}

#[derive(Clone)]
pub(crate) struct DropType(pub usize);

impl Drop for DropType {
    fn drop(&mut self) {
        SIDE_EFFECT.fetch_add(self.0, atomic::Ordering::SeqCst);
    }
}
