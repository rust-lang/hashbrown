use crate::raw::{Allocator, RawTable};
use crate::{HashMap, HashSet};
use paralight::iter::{
    IntoParallelRefMutSource, IntoParallelRefSource, ParallelSource, SourceCleanup,
    SourceDescriptor,
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
        // SAFETY: TODO
        let full = unsafe { self.table.is_bucket_full(index) };
        if full {
            // SAFETY: TODO
            let bucket = unsafe { self.table.bucket(index) };
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
        // SAFETY: TODO
        let full = unsafe { self.table.is_bucket_full(index) };
        if full {
            // SAFETY: TODO
            let bucket = unsafe { self.table.bucket(index) };
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

#[cfg(test)]
mod test {
    use super::*;
    use alloc::boxed::Box;
    use core::ops::Deref;
    use paralight::iter::{ParallelIteratorExt, ParallelSourceExt};
    use paralight::{CpuPinningPolicy, RangeStrategy, ThreadCount, ThreadPoolBuilder};

    #[test]
    fn test_set_par_iter() {
        let mut set = HashSet::new();
        for i in 1..=42 {
            set.insert(Box::new(i));
        }

        let mut thread_pool = ThreadPoolBuilder {
            num_threads: ThreadCount::AvailableParallelism,
            range_strategy: RangeStrategy::WorkStealing,
            cpu_pinning: CpuPinningPolicy::No,
        }
        .build();

        let sum = set
            .par_iter()
            .with_thread_pool(&mut thread_pool)
            .filter_map(|x| x.map(|y| y.deref()))
            .sum::<i32>();
        assert_eq!(sum, 21 * 43);
    }

    #[test]
    fn test_map_par_iter() {
        let mut map = HashMap::new();
        for i in 1..=42 {
            map.insert(Box::new(i), Box::new(i * i));
        }

        let mut thread_pool = ThreadPoolBuilder {
            num_threads: ThreadCount::AvailableParallelism,
            range_strategy: RangeStrategy::WorkStealing,
            cpu_pinning: CpuPinningPolicy::No,
        }
        .build();

        map.par_iter()
            .with_thread_pool(&mut thread_pool)
            .filter_map(|x| x)
            .for_each(|(k, v)| assert_eq!(**k * **k, **v));
    }

    #[test]
    fn test_map_par_iter_mut() {
        let mut map = HashMap::new();
        for i in 1..=42 {
            map.insert(Box::new(i), Box::new(i));
        }

        let mut thread_pool = ThreadPoolBuilder {
            num_threads: ThreadCount::AvailableParallelism,
            range_strategy: RangeStrategy::WorkStealing,
            cpu_pinning: CpuPinningPolicy::No,
        }
        .build();

        map.par_iter_mut()
            .with_thread_pool(&mut thread_pool)
            .filter_map(|x| x)
            .for_each(|(k, v)| **v *= **k);

        for (k, v) in map.iter() {
            assert_eq!(**k * **k, **v);
        }
    }
}
