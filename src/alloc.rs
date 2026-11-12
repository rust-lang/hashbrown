pub(crate) use core::alloc::Allocator;
pub(crate) use stdalloc::alloc::Global;

#[cfg(test)]
pub(crate) use core::alloc::AllocError;
