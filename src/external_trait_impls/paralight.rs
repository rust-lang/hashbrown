use crate::raw::{Allocator, RawTable};
use crate::{HashMap, HashSet};
use paralight::iter::{
    IntoParallelRefMutSource, IntoParallelRefSource, IntoParallelSource, ParallelSource,
    SourceCleanup, SourceDescriptor,
};

// HashSet.par_iter()
impl<'data, T: Sync + 'data, S: 'data, A: Allocator + Sync + 'data> IntoParallelRefSource<'data>
    for HashSet<T, S, A>
{
    type Item = Option<&'data T>;
    type Source = HashSetRefParallelSource<'data, T, S, A>;

    fn par_iter(&'data self) -> Self::Source {
        HashSetRefParallelSource { hash_set: self }
    }
}

#[must_use = "iterator adaptors are lazy"]
pub struct HashSetRefParallelSource<'data, T, S, A: Allocator> {
    hash_set: &'data HashSet<T, S, A>,
}

impl<'data, T: Sync, S, A: Allocator + Sync> ParallelSource
    for HashSetRefParallelSource<'data, T, S, A>
{
    type Item = Option<&'data T>;

    fn descriptor(self) -> impl SourceDescriptor<Item = Self::Item> + Sync {
        HashSetRefSourceDescriptor {
            table: &self.hash_set.map.table,
        }
    }
}

struct HashSetRefSourceDescriptor<'data, T: Sync, A: Allocator> {
    table: &'data RawTable<(T, ()), A>,
}

impl<T: Sync, A: Allocator> SourceCleanup for HashSetRefSourceDescriptor<'_, T, A> {
    const NEEDS_CLEANUP: bool = false;

    unsafe fn cleanup_item_range(&self, _range: core::ops::Range<usize>) {
        // Nothing to cleanup
    }
}

impl<'data, T: Sync, A: Allocator> SourceDescriptor for HashSetRefSourceDescriptor<'data, T, A> {
    type Item = Option<&'data T>;

    fn len(&self) -> usize {
        self.table.buckets()
    }

    unsafe fn fetch_item(&self, index: usize) -> Self::Item {
        debug_assert!(index < self.len());
        // SAFETY: TODO
        let full = unsafe { self.table.is_bucket_full(index) };
        if full {
            // SAFETY: TODO
            let bucket = unsafe { self.table.bucket(index) };
            // SAFETY: TODO
            let (t, ()) = unsafe { bucket.as_ref() };
            Some(t)
        } else {
            None
        }
    }
}

// HashMap.par_iter()
impl<'data, K: Sync + 'data, V: Sync + 'data, S: 'data, A: Allocator + Sync + 'data>
    IntoParallelRefSource<'data> for HashMap<K, V, S, A>
{
    type Item = Option<&'data (K, V)>;
    type Source = HashMapRefParallelSource<'data, K, V, S, A>;

    fn par_iter(&'data self) -> Self::Source {
        HashMapRefParallelSource { hash_map: self }
    }
}

#[must_use = "iterator adaptors are lazy"]
pub struct HashMapRefParallelSource<'data, K, V, S, A: Allocator> {
    hash_map: &'data HashMap<K, V, S, A>,
}

impl<'data, K: Sync, V: Sync, S, A: Allocator + Sync> ParallelSource
    for HashMapRefParallelSource<'data, K, V, S, A>
{
    type Item = Option<&'data (K, V)>;

    fn descriptor(self) -> impl SourceDescriptor<Item = Self::Item> + Sync {
        HashMapRefSourceDescriptor {
            table: &self.hash_map.table,
        }
    }
}

struct HashMapRefSourceDescriptor<'data, K: Sync, V: Sync, A: Allocator> {
    table: &'data RawTable<(K, V), A>,
}

impl<K: Sync, V: Sync, A: Allocator> SourceCleanup for HashMapRefSourceDescriptor<'_, K, V, A> {
    const NEEDS_CLEANUP: bool = false;

    unsafe fn cleanup_item_range(&self, _range: core::ops::Range<usize>) {
        // Nothing to cleanup
    }
}

impl<'data, K: Sync, V: Sync, A: Allocator> SourceDescriptor
    for HashMapRefSourceDescriptor<'data, K, V, A>
{
    type Item = Option<&'data (K, V)>;

    fn len(&self) -> usize {
        self.table.buckets()
    }

    unsafe fn fetch_item(&self, index: usize) -> Self::Item {
        debug_assert!(index < self.len());
        // SAFETY: TODO
        let full = unsafe { self.table.is_bucket_full(index) };
        if full {
            // SAFETY: TODO
            let bucket = unsafe { self.table.bucket(index) };
            // SAFETY: TODO
            unsafe { Some(bucket.as_ref()) }
        } else {
            None
        }
    }
}

// HashMap.par_iter_mut()
// TODO: Remove Sync requirement on V.
impl<'data, K: Sync + 'data, V: Send + Sync + 'data, S: 'data, A: Allocator + Sync + 'data>
    IntoParallelRefMutSource<'data> for HashMap<K, V, S, A>
{
    type Item = Option<(&'data K, &'data mut V)>;
    type Source = HashMapRefMutParallelSource<'data, K, V, S, A>;

    fn par_iter_mut(&'data mut self) -> Self::Source {
        HashMapRefMutParallelSource { hash_map: self }
    }
}

#[must_use = "iterator adaptors are lazy"]
pub struct HashMapRefMutParallelSource<'data, K, V, S, A: Allocator> {
    hash_map: &'data mut HashMap<K, V, S, A>,
}

impl<'data, K: Sync, V: Send + Sync, S, A: Allocator + Sync> ParallelSource
    for HashMapRefMutParallelSource<'data, K, V, S, A>
{
    type Item = Option<(&'data K, &'data mut V)>;

    fn descriptor(self) -> impl SourceDescriptor<Item = Self::Item> + Sync {
        HashMapRefMutSourceDescriptor {
            table: &self.hash_map.table,
        }
    }
}

struct HashMapRefMutSourceDescriptor<'data, K: Sync, V: Send + Sync, A: Allocator> {
    table: &'data RawTable<(K, V), A>,
}

impl<K: Sync, V: Send + Sync, A: Allocator> SourceCleanup
    for HashMapRefMutSourceDescriptor<'_, K, V, A>
{
    const NEEDS_CLEANUP: bool = false;

    unsafe fn cleanup_item_range(&self, _range: core::ops::Range<usize>) {
        // Nothing to cleanup
    }
}

impl<'data, K: Sync, V: Send + Sync, A: Allocator> SourceDescriptor
    for HashMapRefMutSourceDescriptor<'data, K, V, A>
{
    type Item = Option<(&'data K, &'data mut V)>;

    fn len(&self) -> usize {
        self.table.buckets()
    }

    unsafe fn fetch_item(&self, index: usize) -> Self::Item {
        debug_assert!(index < self.len());
        // SAFETY: TODO
        let full = unsafe { self.table.is_bucket_full(index) };
        if full {
            // SAFETY: TODO
            let bucket = unsafe { self.table.bucket(index) };
            // SAFETY: TODO
            let (key, value) = unsafe { bucket.as_mut() };
            Some((key, value))
        } else {
            None
        }
    }
}

// HashSet.into_par_iter()
// TODO: Remove Sync requirement on T.
impl<T: Send + Sync, S, A: Allocator + Sync> IntoParallelSource for HashSet<T, S, A> {
    type Item = Option<T>;
    type Source = HashSetParallelSource<T, S, A>;

    fn into_par_iter(self) -> Self::Source {
        HashSetParallelSource { hash_set: self }
    }
}

#[must_use = "iterator adaptors are lazy"]
pub struct HashSetParallelSource<T, S, A: Allocator> {
    hash_set: HashSet<T, S, A>,
}

impl<T: Send + Sync, S, A: Allocator + Sync> ParallelSource for HashSetParallelSource<T, S, A> {
    type Item = Option<T>;

    fn descriptor(self) -> impl SourceDescriptor<Item = Self::Item> + Sync {
        HashSetSourceDescriptor {
            table: self.hash_set.map.table,
        }
    }
}

struct HashSetSourceDescriptor<T, A: Allocator> {
    table: RawTable<(T, ()), A>,
}

impl<T: Send + Sync, A: Allocator> SourceCleanup for HashSetSourceDescriptor<T, A> {
    const NEEDS_CLEANUP: bool = core::mem::needs_drop::<T>();

    unsafe fn cleanup_item_range(&self, range: core::ops::Range<usize>) {
        if Self::NEEDS_CLEANUP {
            debug_assert!(range.start <= range.end);
            debug_assert!(range.start <= self.len());
            debug_assert!(range.end <= self.len());
            for index in range {
                // SAFETY: TODO
                let full = unsafe { self.table.is_bucket_full(index) };
                if full {
                    // SAFETY: TODO
                    let bucket = unsafe { self.table.bucket(index) };
                    // SAFETY: TODO
                    let (t, ()) = unsafe { bucket.read() };
                    drop(t);
                }
            }
        }
    }
}

impl<T: Send + Sync, A: Allocator> SourceDescriptor for HashSetSourceDescriptor<T, A> {
    type Item = Option<T>;

    fn len(&self) -> usize {
        self.table.buckets()
    }

    unsafe fn fetch_item(&self, index: usize) -> Self::Item {
        debug_assert!(index < self.len());
        // SAFETY: TODO
        let full = unsafe { self.table.is_bucket_full(index) };
        if full {
            // SAFETY: TODO
            let bucket = unsafe { self.table.bucket(index) };
            // SAFETY: TODO
            let (t, ()) = unsafe { bucket.read() };
            Some(t)
        } else {
            None
        }
    }
}

impl<T, A: Allocator> Drop for HashSetSourceDescriptor<T, A> {
    fn drop(&mut self) {
        // Paralight already dropped each missing bucket via calls to cleanup_item_range(), so we
        // can simply mark all buckets as cleared and let the RawTable destructor do the rest.
        // TODO: Optimize this to simply deallocate without touching the control bytes.
        self.table.clear_no_drop();
    }
}

// HashMap.into_par_iter()
// TODO: Remove Sync requirement on K and V.
impl<K: Send + Sync, V: Send + Sync, S, A: Allocator + Sync> IntoParallelSource
    for HashMap<K, V, S, A>
{
    type Item = Option<(K, V)>;
    type Source = HashMapParallelSource<K, V, S, A>;

    fn into_par_iter(self) -> Self::Source {
        HashMapParallelSource { hash_map: self }
    }
}

#[must_use = "iterator adaptors are lazy"]
pub struct HashMapParallelSource<K, V, S, A: Allocator> {
    hash_map: HashMap<K, V, S, A>,
}

impl<K: Send + Sync, V: Send + Sync, S, A: Allocator + Sync> ParallelSource
    for HashMapParallelSource<K, V, S, A>
{
    type Item = Option<(K, V)>;

    fn descriptor(self) -> impl SourceDescriptor<Item = Self::Item> + Sync {
        HashMapSourceDescriptor {
            table: self.hash_map.table,
        }
    }
}

struct HashMapSourceDescriptor<K, V, A: Allocator> {
    table: RawTable<(K, V), A>,
}

impl<K: Send + Sync, V: Send + Sync, A: Allocator> SourceCleanup
    for HashMapSourceDescriptor<K, V, A>
{
    const NEEDS_CLEANUP: bool = core::mem::needs_drop::<(K, V)>();

    unsafe fn cleanup_item_range(&self, range: core::ops::Range<usize>) {
        if Self::NEEDS_CLEANUP {
            debug_assert!(range.start <= range.end);
            debug_assert!(range.start <= self.len());
            debug_assert!(range.end <= self.len());
            for index in range {
                // SAFETY: TODO
                let full = unsafe { self.table.is_bucket_full(index) };
                if full {
                    // SAFETY: TODO
                    let bucket = unsafe { self.table.bucket(index) };
                    // SAFETY: TODO
                    let key_value = unsafe { bucket.read() };
                    drop(key_value);
                }
            }
        }
    }
}

impl<K: Send + Sync, V: Send + Sync, A: Allocator> SourceDescriptor
    for HashMapSourceDescriptor<K, V, A>
{
    type Item = Option<(K, V)>;

    fn len(&self) -> usize {
        self.table.buckets()
    }

    unsafe fn fetch_item(&self, index: usize) -> Self::Item {
        debug_assert!(index < self.len());
        // SAFETY: TODO
        let full = unsafe { self.table.is_bucket_full(index) };
        if full {
            // SAFETY: TODO
            let bucket = unsafe { self.table.bucket(index) };
            // SAFETY: TODO
            unsafe { Some(bucket.read()) }
        } else {
            None
        }
    }
}

impl<K, V, A: Allocator> Drop for HashMapSourceDescriptor<K, V, A> {
    fn drop(&mut self) {
        // Paralight already dropped each missing bucket via calls to cleanup_item_range(), so we
        // can simply mark all buckets as cleared and let the RawTable destructor do the rest.
        // TODO: Optimize this to simply deallocate without touching the control bytes.
        self.table.clear_no_drop();
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use alloc::boxed::Box;
    use core::ops::Deref;
    use paralight::iter::{ParallelIteratorExt, ParallelSourceExt};
    use paralight::{CpuPinningPolicy, RangeStrategy, ThreadCount, ThreadPoolBuilder};

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
            .filter_map(|x| x.map(|y| y.deref()))
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
            .filter_map(|x| x.map(|y| *y))
            .sum::<i32>();
        assert_eq!(sum, 21 * 43);
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
            .filter_map(|x| x)
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
            .filter_map(|x| x)
            .for_each(|(k, v)| **v *= **k);

        for (k, v) in map.iter() {
            assert_eq!(**k * **k, **v);
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
            .filter_map(|x| x)
            .for_each(|(k, v)| assert_eq!(*k * *k, *v));
    }
}
