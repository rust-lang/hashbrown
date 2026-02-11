#![forbid(
    unsafe_op_in_unsafe_fn,
    clippy::multiple_unsafe_ops_per_block,
    clippy::undocumented_unsafe_blocks
)]

use crate::alloc::Allocator;
use crate::{HashMap, HashSet};
use paralight::iter::{
    IntoParallelRefMutSource, IntoParallelRefSource, IntoParallelSource, ParallelSource,
    SimpleSourceDescriptor, SourceCleanup, SourceDescriptor,
};

// HashSet.par_iter()
impl<'data, T: Sync + 'data, S: 'data, A: Allocator + 'data> IntoParallelRefSource<'data>
    for HashSet<T, S, A>
{
    type Item = &'data T;
    type Source = HashSetRefParallelSource<'data, T, S, A>;

    fn par_iter(&'data self) -> Self::Source {
        HashSetRefParallelSource { hash_set: self }
    }
}

#[must_use = "iterator adaptors are lazy"]
pub struct HashSetRefParallelSource<'data, T, S, A: Allocator> {
    hash_set: &'data HashSet<T, S, A>,
}

impl<'data, T: Sync, S, A: Allocator> ParallelSource for HashSetRefParallelSource<'data, T, S, A> {
    type Item = &'data T;

    fn descriptor(self) -> impl SourceDescriptor<Item = Self::Item> + Sync {
        HashSetRefSourceDescriptor {
            table: raw_table_wrapper::HashSetRef {
                inner: &self.hash_set.map.table,
            },
        }
    }
}

struct HashSetRefSourceDescriptor<'data, T: Sync, A: Allocator> {
    table: raw_table_wrapper::HashSetRef<'data, T, A>,
}

impl<T: Sync, A: Allocator> SourceCleanup for HashSetRefSourceDescriptor<'_, T, A> {
    const NEEDS_CLEANUP: bool = false;

    fn len(&self) -> usize {
        self.table.inner.num_buckets()
    }

    unsafe fn cleanup_item_range(&self, _range: core::ops::Range<usize>) {
        // Nothing to cleanup
    }
}

impl<'data, T: Sync, A: Allocator> SimpleSourceDescriptor
    for HashSetRefSourceDescriptor<'data, T, A>
{
    type Item = &'data T;

    unsafe fn simple_fetch_item(&self, index: usize) -> Option<Self::Item> {
        debug_assert!(index < self.len());
        // SAFETY: The passed index is less than the number of buckets. This is
        // ensured by the safety preconditions of `fetch_item()`, given that
        // `len()` returned the number of buckets, and is further confirmed by
        // the debug assertion.
        let full = unsafe { self.table.inner.is_bucket_full(index) };
        if full {
            // SAFETY:
            // - The table is already allocated.
            // - The index is in bounds (see previous safety comment).
            // - The table contains elements of type (T, ()).
            let bucket = unsafe { self.table.inner.bucket(index) };
            // SAFETY: The bucket is full, so it's safe to derive a const
            // reference from it.
            let (t, ()) = unsafe { bucket.as_ref() };
            Some(t)
        } else {
            None
        }
    }
}

// HashMap.par_iter()
impl<'data, K: Sync + 'data, V: Sync + 'data, S: 'data, A: Allocator + 'data>
    IntoParallelRefSource<'data> for HashMap<K, V, S, A>
{
    type Item = &'data (K, V);
    type Source = HashMapRefParallelSource<'data, K, V, S, A>;

    fn par_iter(&'data self) -> Self::Source {
        HashMapRefParallelSource { hash_map: self }
    }
}

#[must_use = "iterator adaptors are lazy"]
pub struct HashMapRefParallelSource<'data, K, V, S, A: Allocator> {
    hash_map: &'data HashMap<K, V, S, A>,
}

impl<'data, K: Sync, V: Sync, S, A: Allocator> ParallelSource
    for HashMapRefParallelSource<'data, K, V, S, A>
{
    type Item = &'data (K, V);

    fn descriptor(self) -> impl SourceDescriptor<Item = Self::Item> + Sync {
        HashMapRefSourceDescriptor {
            table: raw_table_wrapper::HashMapRef {
                inner: &self.hash_map.table,
            },
        }
    }
}

struct HashMapRefSourceDescriptor<'data, K: Sync, V: Sync, A: Allocator> {
    table: raw_table_wrapper::HashMapRef<'data, K, V, A>,
}

impl<K: Sync, V: Sync, A: Allocator> SourceCleanup for HashMapRefSourceDescriptor<'_, K, V, A> {
    const NEEDS_CLEANUP: bool = false;

    fn len(&self) -> usize {
        self.table.inner.num_buckets()
    }

    unsafe fn cleanup_item_range(&self, _range: core::ops::Range<usize>) {
        // Nothing to cleanup
    }
}

impl<'data, K: Sync, V: Sync, A: Allocator> SimpleSourceDescriptor
    for HashMapRefSourceDescriptor<'data, K, V, A>
{
    type Item = &'data (K, V);

    unsafe fn simple_fetch_item(&self, index: usize) -> Option<Self::Item> {
        debug_assert!(index < self.len());
        // SAFETY: The passed index is less than the number of buckets. This is
        // ensured by the safety preconditions of `fetch_item()`, given that
        // `len()` returned the number of buckets, and is further confirmed by
        // the debug assertion.
        let full = unsafe { self.table.inner.is_bucket_full(index) };
        if full {
            // SAFETY:
            // - The table is already allocated.
            // - The index is in bounds (see previous safety comment).
            // - The table contains elements of type (K, V).
            let bucket = unsafe { self.table.inner.bucket(index) };
            // SAFETY: The bucket is full, so it's safe to derive a const
            // reference from it.
            unsafe { Some(bucket.as_ref()) }
        } else {
            None
        }
    }
}

// HashMap.par_iter_mut()
impl<'data, K: Sync + 'data, V: Send + 'data, S: 'data, A: Allocator + 'data>
    IntoParallelRefMutSource<'data> for HashMap<K, V, S, A>
{
    type Item = (&'data K, &'data mut V);
    type Source = HashMapRefMutParallelSource<'data, K, V, S, A>;

    fn par_iter_mut(&'data mut self) -> Self::Source {
        HashMapRefMutParallelSource { hash_map: self }
    }
}

#[must_use = "iterator adaptors are lazy"]
pub struct HashMapRefMutParallelSource<'data, K, V, S, A: Allocator> {
    hash_map: &'data mut HashMap<K, V, S, A>,
}

impl<'data, K: Sync, V: Send, S, A: Allocator> ParallelSource
    for HashMapRefMutParallelSource<'data, K, V, S, A>
{
    type Item = (&'data K, &'data mut V);

    fn descriptor(self) -> impl SourceDescriptor<Item = Self::Item> + Sync {
        HashMapRefMutSourceDescriptor {
            table: raw_table_wrapper::HashMapRefMut {
                inner: &self.hash_map.table,
            },
        }
    }
}

struct HashMapRefMutSourceDescriptor<'data, K: Sync, V: Send, A: Allocator> {
    table: raw_table_wrapper::HashMapRefMut<'data, K, V, A>,
}

impl<K: Sync, V: Send, A: Allocator> SourceCleanup for HashMapRefMutSourceDescriptor<'_, K, V, A> {
    const NEEDS_CLEANUP: bool = false;

    fn len(&self) -> usize {
        self.table.inner.num_buckets()
    }

    unsafe fn cleanup_item_range(&self, _range: core::ops::Range<usize>) {
        // Nothing to cleanup
    }
}

impl<'data, K: Sync, V: Send, A: Allocator> SimpleSourceDescriptor
    for HashMapRefMutSourceDescriptor<'data, K, V, A>
{
    type Item = (&'data K, &'data mut V);

    unsafe fn simple_fetch_item(&self, index: usize) -> Option<Self::Item> {
        debug_assert!(index < self.len());
        // SAFETY: The passed index is less than the number of buckets. This is
        // ensured by the safety preconditions of `fetch_item()`, given that
        // `len()` returned the number of buckets, and is further confirmed by
        // the debug assertion.
        let full = unsafe { self.table.inner.is_bucket_full(index) };
        if full {
            // SAFETY:
            // - The table is already allocated.
            // - The index is in bounds (see previous safety comment).
            // - The table contains elements of type (K, V).
            let bucket = unsafe { self.table.inner.bucket(index) };
            // SAFETY:
            // - The bucket is full, i.e. points to a valid value.
            // - While the resulting reference is valid, the memory it points to
            //   isn't accessed through any other pointer. Indeed, the
            //   `SourceDescriptor` contract ensures that no other call to
            //   `fetch_item()` will be made at this index while the iterator is
            //   active. Furthermore, `HashMapRefMutParallelSource` holds a
            //   mutable reference to the hash map with the 'data lifetime,
            //   ensuring that no other part of the program accesses the hash
            //   map while the returned reference exists.
            let (key, value) = unsafe { bucket.as_mut() };
            Some((key, value))
        } else {
            None
        }
    }
}

// HashSet.into_par_iter()
impl<T: Send, S, A: Allocator> IntoParallelSource for HashSet<T, S, A> {
    type Item = T;
    type Source = HashSetParallelSource<T, S, A>;

    fn into_par_iter(self) -> Self::Source {
        HashSetParallelSource { hash_set: self }
    }
}

#[must_use = "iterator adaptors are lazy"]
pub struct HashSetParallelSource<T, S, A: Allocator> {
    hash_set: HashSet<T, S, A>,
}

impl<T: Send, S, A: Allocator> ParallelSource for HashSetParallelSource<T, S, A> {
    type Item = T;

    fn descriptor(self) -> impl SourceDescriptor<Item = Self::Item> + Sync {
        HashSetSourceDescriptor {
            table: raw_table_wrapper::HashSet {
                inner: self.hash_set.map.table,
            },
        }
    }
}

struct HashSetSourceDescriptor<T, A: Allocator> {
    table: raw_table_wrapper::HashSet<T, A>,
}

impl<T: Send, A: Allocator> SourceCleanup for HashSetSourceDescriptor<T, A> {
    const NEEDS_CLEANUP: bool = core::mem::needs_drop::<T>();

    fn len(&self) -> usize {
        self.table.inner.num_buckets()
    }

    unsafe fn cleanup_item_range(&self, range: core::ops::Range<usize>) {
        if Self::NEEDS_CLEANUP {
            debug_assert!(range.start <= range.end);
            debug_assert!(range.start <= self.len());
            debug_assert!(range.end <= self.len());
            for index in range {
                // SAFETY: The passed index is less than the number of buckets. This is
                // ensured by the safety preconditions of `cleanup_item_range()`, given
                // that `len()` returned the number of buckets, and is further confirmed
                // by the debug assertions.
                let full = unsafe { self.table.inner.is_bucket_full(index) };
                if full {
                    // SAFETY:
                    // - The table is already allocated.
                    // - The index is in bounds (see previous safety comment).
                    // - The table contains elements of type (T, ()).
                    let bucket = unsafe { self.table.inner.bucket(index) };
                    // SAFETY:
                    // - The bucket points to an aligned value of type (T, ()).
                    // - The value is initialized, as the bucket is full.
                    // - No other part of the program reads it, as the `SourceCleanup`
                    //   and `SourceDescriptor` contracts ensure that no other call to
                    //   `fetch_item()` nor `cleanup_item_range()` is made for this
                    //   index; and even though the bucket isn't marked as empty here,
                    //   the Drop implementation clears the table without dropping.
                    let (t, ()) = unsafe { bucket.read() };
                    drop(t);
                }
            }
        }
    }
}

impl<T: Send, A: Allocator> SimpleSourceDescriptor for HashSetSourceDescriptor<T, A> {
    type Item = T;

    unsafe fn simple_fetch_item(&self, index: usize) -> Option<Self::Item> {
        debug_assert!(index < self.len());
        // SAFETY: The passed index is less than the number of buckets. This is
        // ensured by the safety preconditions of `fetch_item()`, given that
        // `len()` returned the number of buckets, and is further confirmed by
        // the debug assertion.
        let full = unsafe { self.table.inner.is_bucket_full(index) };
        if full {
            // SAFETY:
            // - The table is already allocated.
            // - The index is in bounds (see previous safety comment).
            // - The table contains elements of type (T, ()).
            let bucket = unsafe { self.table.inner.bucket(index) };
            // SAFETY:
            // - The bucket points to an aligned value of type (T, ()).
            // - The value is initialized, as the bucket is full.
            // - No other part of the program reads it, as the `SourceCleanup`
            //   and `SourceDescriptor` contracts ensure that no other call to
            //   `fetch_item()` nor `cleanup_item_range()` is made for this
            //   index; and even though the bucket isn't marked as empty here,
            //   the Drop implementation clears the table without dropping.
            let (t, ()) = unsafe { bucket.read() };
            Some(t)
        } else {
            None
        }
    }
}

impl<T, A: Allocator> Drop for HashSetSourceDescriptor<T, A> {
    fn drop(&mut self) {
        // SAFETY:
        // Paralight already dropped each missing* bucket via calls to cleanup_item_range(), so we
        // can simply mark all buckets as cleared and let the RawTable destructor do the rest.
        //
        // *Some buckets may be missing because the iterator exited early (e.g. an item was found
        // via the find_any() adaptor) or unexpectedly due to a panic (e.g. in the closure passed
        // to the for_each() adaptor).
        unsafe {
            self.table.inner.deallocate_cleared_table();
        }
    }
}

// HashMap.into_par_iter()
impl<K: Send, V: Send, S, A: Allocator> IntoParallelSource for HashMap<K, V, S, A> {
    type Item = (K, V);
    type Source = HashMapParallelSource<K, V, S, A>;

    fn into_par_iter(self) -> Self::Source {
        HashMapParallelSource { hash_map: self }
    }
}

#[must_use = "iterator adaptors are lazy"]
pub struct HashMapParallelSource<K, V, S, A: Allocator> {
    hash_map: HashMap<K, V, S, A>,
}

impl<K: Send, V: Send, S, A: Allocator> ParallelSource for HashMapParallelSource<K, V, S, A> {
    type Item = (K, V);

    fn descriptor(self) -> impl SourceDescriptor<Item = Self::Item> + Sync {
        HashMapSourceDescriptor {
            table: raw_table_wrapper::HashMap {
                inner: self.hash_map.table,
            },
        }
    }
}

struct HashMapSourceDescriptor<K, V, A: Allocator> {
    table: raw_table_wrapper::HashMap<K, V, A>,
}

impl<K: Send, V: Send, A: Allocator> SourceCleanup for HashMapSourceDescriptor<K, V, A> {
    const NEEDS_CLEANUP: bool = core::mem::needs_drop::<(K, V)>();

    fn len(&self) -> usize {
        self.table.inner.num_buckets()
    }

    unsafe fn cleanup_item_range(&self, range: core::ops::Range<usize>) {
        if Self::NEEDS_CLEANUP {
            debug_assert!(range.start <= range.end);
            debug_assert!(range.start <= self.len());
            debug_assert!(range.end <= self.len());
            for index in range {
                // SAFETY: The passed index is less than the number of buckets. This is
                // ensured by the safety preconditions of `cleanup_item_range()`, given
                // that `len()` returned the number of buckets, and is further confirmed
                // by the debug assertions.
                let full = unsafe { self.table.inner.is_bucket_full(index) };
                if full {
                    // SAFETY:
                    // - The table is already allocated.
                    // - The index is in bounds (see previous safety comment).
                    // - The table contains elements of type (K, V).
                    let bucket = unsafe { self.table.inner.bucket(index) };
                    // SAFETY:
                    // - The bucket points to an aligned value of type (K, V).
                    // - The value is initialized, as the bucket is full.
                    // - No other part of the program reads it, as the `SourceCleanup`
                    //   and `SourceDescriptor` contracts ensure that no other call to
                    //   `fetch_item()` nor `cleanup_item_range()` is made for this
                    //   index; and even though the bucket isn't marked as empty here,
                    //   the Drop implementation clears the table without dropping.
                    let key_value = unsafe { bucket.read() };
                    drop(key_value);
                }
            }
        }
    }
}

impl<K: Send, V: Send, A: Allocator> SimpleSourceDescriptor for HashMapSourceDescriptor<K, V, A> {
    type Item = (K, V);

    unsafe fn simple_fetch_item(&self, index: usize) -> Option<Self::Item> {
        debug_assert!(index < self.len());
        // SAFETY: The passed index is less than the number of buckets. This is
        // ensured by the safety preconditions of `fetch_item()`, given that
        // `len()` returned the number of buckets, and is further confirmed by
        // the debug assertion.
        let full = unsafe { self.table.inner.is_bucket_full(index) };
        if full {
            // SAFETY:
            // - The table is already allocated.
            // - The index is in bounds (see previous safety comment).
            // - The table contains elements of type (K, V).
            let bucket = unsafe { self.table.inner.bucket(index) };
            // SAFETY:
            // - The bucket points to an aligned value of type (K, V).
            // - The value is initialized, as the bucket is full.
            // - No other part of the program reads it, as the `SourceCleanup`
            //   and `SourceDescriptor` contracts ensure that no other call to
            //   `fetch_item()` nor `cleanup_item_range()` is made for this
            //   index; and even though the bucket isn't marked as empty here,
            //   the Drop implementation clears the table without dropping.
            unsafe { Some(bucket.read()) }
        } else {
            None
        }
    }
}

impl<K, V, A: Allocator> Drop for HashMapSourceDescriptor<K, V, A> {
    fn drop(&mut self) {
        // SAFETY:
        // Paralight already dropped each missing* bucket via calls to cleanup_item_range(), so we
        // can simply mark all buckets as cleared and let the RawTable destructor do the rest.
        //
        // *Some buckets may be missing because the iterator exited early (e.g. an item was found
        // via the find_any() adaptor) or unexpectedly due to a panic (e.g. in the closure passed
        // to the for_each() adaptor).
        unsafe {
            self.table.inner.deallocate_cleared_table();
        }
    }
}

mod raw_table_wrapper {
    use crate::alloc::Allocator;
    use crate::raw::RawTable;

    /// Helper to implement HashSet::par_iter().
    pub(super) struct HashSetRef<'data, T, A: Allocator> {
        pub(super) inner: &'data RawTable<(T, ()), A>,
    }

    // SAFETY:
    // - This wrapper type is shared with worker threads, that extract references of type `&T`.
    //   This requires `&T: Send`. Therefore, this wrapper is Sync if and only if `T` is Sync.
    // - The allocator doesn't need any Send/Sync bounds, because the parallel iterators neither
    //   allocate nor deallocate the hash table.
    unsafe impl<T: Sync, A: Allocator> Sync for HashSetRef<'_, T, A> {}

    /// Helper to implement HashMap::par_iter().
    pub(super) struct HashMapRef<'data, K, V, A: Allocator> {
        pub(super) inner: &'data RawTable<(K, V), A>,
    }

    // SAFETY:
    // - This wrapper type is shared with worker threads, that extract references of type
    //   `(&K, &V)`. This requires `(&K, &V): Send`. Therefore, this wrapper is Sync if and only
    //   if `K` and `V` are Sync.
    // - The allocator doesn't need any Send/Sync bounds, because the parallel iterators neither
    //   allocate nor deallocate the hash table.
    unsafe impl<K: Sync, V: Sync, A: Allocator> Sync for HashMapRef<'_, K, V, A> {}

    /// Helper to implement HashMap::par_iter_mut().
    pub(super) struct HashMapRefMut<'data, K, V, A: Allocator> {
        pub(super) inner: &'data RawTable<(K, V), A>,
    }

    // SAFETY:
    // - This wrapper type is shared with worker threads, that extract references of type
    //   `(&K, &mut V)`. This requires `(&K, &mut V): Send`. Therefore, this wrapper is Sync if
    //   and only if `K` is Sync and `V` is Send.
    // - The allocator doesn't need any Send/Sync bounds, because the parallel iterators neither
    //   allocate nor deallocate the hash table.
    unsafe impl<K: Sync, V: Send, A: Allocator> Sync for HashMapRefMut<'_, K, V, A> {}

    /// Helper to implement HashSet::into_par_iter().
    pub(super) struct HashSet<T, A: Allocator> {
        pub(super) inner: RawTable<(T, ()), A>,
    }

    // SAFETY:
    // - This wrapper type is shared with worker threads, that extract values of type `T`.
    //   Therefore, this wrapper is Sync if and only if `T` is Send.
    // - The allocator doesn't need any Send/Sync bounds, because the parallel iterators neither
    //   allocate nor deallocate the hash table. Note that `HashSetSourceDescriptor::drop`
    //   deallocates the hash table, but that's unrelated to this Sync bound (`drop()` takes a
    //   `&mut self` input, so only Send bounds are relevant for that).
    unsafe impl<T: Send, A: Allocator> Sync for HashSet<T, A> {}

    /// Helper to implement HashMap::into_par_iter().
    pub(super) struct HashMap<K, V, A: Allocator> {
        pub(super) inner: RawTable<(K, V), A>,
    }

    // SAFETY:
    // - This wrapper type is shared with worker threads, that extract values of type `(K, V)`.
    //   This requires `(K, V): Send`. Therefore, this wrapper is Sync if and only if `K` and `V`
    //   are Send.
    // - The allocator doesn't need any Send/Sync bounds, because the parallel iterators neither
    //   allocate nor deallocate the hash table.  Note that `HashMapSourceDescriptor::drop`
    //   deallocates the hash table, but that's unrelated to this Sync bound (`drop()` takes a
    //   `&mut self` input, so only Send bounds are relevant for that).
    unsafe impl<K: Send, V: Send, A: Allocator> Sync for HashMap<K, V, A> {}
}

#[cfg(test)]
mod test {
    use super::*;
    use core::cell::Cell;
    use core::ops::Deref;
    use paralight::iter::{ParallelIteratorExt, ParallelSourceExt};
    use paralight::threads::{CpuPinningPolicy, RangeStrategy, ThreadCount, ThreadPoolBuilder};
    use std::hash::{Hash, Hasher};
    use stdalloc::boxed::Box;

    // A cell that implements Hash.
    #[derive(PartialEq, Eq)]
    struct HashCell<T: Copy>(Cell<T>);

    impl<T: Copy> HashCell<T> {
        fn new(t: T) -> Self {
            Self(Cell::new(t))
        }

        fn get(&self) -> T {
            self.0.get()
        }
    }

    impl<T: Copy + Hash> Hash for HashCell<T> {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.0.get().hash(state)
        }
    }

    #[test]
    fn test_set_par_iter() {
        let mut thread_pool = ThreadPoolBuilder {
            num_threads: ThreadCount::AvailableParallelism,
            range_strategy: RangeStrategy::WorkStealing,
            cpu_pinning: CpuPinningPolicy::No,
        }
        .build();

        let mut set = HashSet::new();
        for i in 1..=42 {
            set.insert(Box::new(i));
        }

        let sum = set
            .par_iter()
            .with_thread_pool(&mut thread_pool)
            .map(|x| x.deref())
            .sum::<i32>();
        assert_eq!(sum, 21 * 43);
    }

    #[test]
    fn test_set_into_par_iter() {
        let mut thread_pool = ThreadPoolBuilder {
            num_threads: ThreadCount::AvailableParallelism,
            range_strategy: RangeStrategy::WorkStealing,
            cpu_pinning: CpuPinningPolicy::No,
        }
        .build();

        let mut set = HashSet::new();
        for i in 1..=42 {
            set.insert(Box::new(i));
        }

        let sum = set
            .into_par_iter()
            .with_thread_pool(&mut thread_pool)
            .map(|x| *x)
            .sum::<i32>();
        assert_eq!(sum, 21 * 43);
    }

    #[test]
    fn test_set_into_par_iter_send() {
        let mut thread_pool = ThreadPoolBuilder {
            num_threads: ThreadCount::AvailableParallelism,
            range_strategy: RangeStrategy::WorkStealing,
            cpu_pinning: CpuPinningPolicy::No,
        }
        .build();

        let mut set = HashSet::new();
        for i in 1..=42 {
            set.insert(HashCell::new(i));
        }

        let sum = set
            .into_par_iter()
            .with_thread_pool(&mut thread_pool)
            .map(|x| x.get())
            .sum::<i32>();
        assert_eq!(sum, 21 * 43);
    }

    #[test]
    fn test_set_into_par_iter_find() {
        let mut thread_pool = ThreadPoolBuilder {
            num_threads: ThreadCount::AvailableParallelism,
            range_strategy: RangeStrategy::WorkStealing,
            cpu_pinning: CpuPinningPolicy::No,
        }
        .build();

        let mut set = HashSet::new();
        for i in 1..=42 {
            set.insert(Box::new(i));
        }

        // The search will exit once an even number is found, this test checks
        // (with Miri) that no memory leak happens as a result.
        let any_even = set
            .into_par_iter()
            .with_thread_pool(&mut thread_pool)
            .find_any(|x| **x % 2 == 0);
        assert!(any_even.is_some());
        assert_eq!(*any_even.unwrap() % 2, 0);
    }

    #[test]
    fn test_map_par_iter() {
        let mut thread_pool = ThreadPoolBuilder {
            num_threads: ThreadCount::AvailableParallelism,
            range_strategy: RangeStrategy::WorkStealing,
            cpu_pinning: CpuPinningPolicy::No,
        }
        .build();

        let mut map = HashMap::new();
        for i in 1..=42 {
            map.insert(Box::new(i), Box::new(i * i));
        }

        map.par_iter()
            .with_thread_pool(&mut thread_pool)
            .for_each(|(k, v)| assert_eq!(**k * **k, **v));
    }

    #[test]
    fn test_map_par_iter_mut() {
        let mut thread_pool = ThreadPoolBuilder {
            num_threads: ThreadCount::AvailableParallelism,
            range_strategy: RangeStrategy::WorkStealing,
            cpu_pinning: CpuPinningPolicy::No,
        }
        .build();

        let mut map = HashMap::new();
        for i in 1..=42 {
            map.insert(Box::new(i), Box::new(i));
        }

        map.par_iter_mut()
            .with_thread_pool(&mut thread_pool)
            .for_each(|(k, v)| **v *= **k);

        for (k, v) in map.iter() {
            assert_eq!(**k * **k, **v);
        }
    }

    #[test]
    fn test_map_par_iter_mut_send_sync() {
        let mut thread_pool = ThreadPoolBuilder {
            num_threads: ThreadCount::AvailableParallelism,
            range_strategy: RangeStrategy::WorkStealing,
            cpu_pinning: CpuPinningPolicy::No,
        }
        .build();

        let mut map = HashMap::new();
        for i in 1..=42 {
            map.insert(Box::new(i), Cell::new(i));
        }

        map.par_iter_mut()
            .with_thread_pool(&mut thread_pool)
            .for_each(|(k, v)| *v.get_mut() *= **k);

        for (k, v) in map.iter() {
            assert_eq!(**k * **k, v.get());
        }
    }

    #[test]
    fn test_map_into_par_iter() {
        let mut thread_pool = ThreadPoolBuilder {
            num_threads: ThreadCount::AvailableParallelism,
            range_strategy: RangeStrategy::WorkStealing,
            cpu_pinning: CpuPinningPolicy::No,
        }
        .build();

        let mut map = HashMap::new();
        for i in 1..=42 {
            map.insert(Box::new(i), Box::new(i * i));
        }

        map.into_par_iter()
            .with_thread_pool(&mut thread_pool)
            .for_each(|(k, v)| assert_eq!(*k * *k, *v));
    }

    #[test]
    fn test_map_into_par_iter_send() {
        let mut thread_pool = ThreadPoolBuilder {
            num_threads: ThreadCount::AvailableParallelism,
            range_strategy: RangeStrategy::WorkStealing,
            cpu_pinning: CpuPinningPolicy::No,
        }
        .build();

        let mut map = HashMap::new();
        for i in 1..=42 {
            map.insert(HashCell::new(i), Cell::new(i * i));
        }

        map.into_par_iter()
            .with_thread_pool(&mut thread_pool)
            .for_each(|(k, v)| assert_eq!(k.get() * k.get(), v.get()));
    }

    #[test]
    fn test_map_into_par_iter_find() {
        let mut thread_pool = ThreadPoolBuilder {
            num_threads: ThreadCount::AvailableParallelism,
            range_strategy: RangeStrategy::WorkStealing,
            cpu_pinning: CpuPinningPolicy::No,
        }
        .build();

        let mut map = HashMap::new();
        for i in 1..=42 {
            map.insert(Box::new(i), Box::new(i * i));
        }

        // The search will exit once an match is found, this test checks (with
        // Miri) that no memory leak happens as a result.
        let needle = map
            .into_par_iter()
            .with_thread_pool(&mut thread_pool)
            .find_any(|(k, v)| **k % 2 == 0 && **v % 3 == 0);
        assert!(needle.is_some());
        let (k, v) = needle.unwrap();
        assert_eq!(*k % 2, 0);
        assert_eq!(*v % 3, 0);
    }
}
