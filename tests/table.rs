//! Tests for insertion into a hash table without growing it.

use hashbrown::HashTable;
use hashbrown::hash_table::OccupiedEntry;
use std::cell::Cell;

#[derive(Clone, Copy)]
enum Insertion {
    WithoutRehash,
    WithinCapacity,
}

const INSERTIONS: [Insertion; 2] = [Insertion::WithoutRehash, Insertion::WithinCapacity];

impl Insertion {
    fn insert<T>(
        self,
        table: &mut HashTable<T>,
        hash: u64,
        value: T,
        hasher: impl Fn(&T) -> u64,
    ) -> Result<OccupiedEntry<'_, T>, T> {
        match self {
            Self::WithoutRehash => table.try_insert_unique_without_rehash(hash, value),
            Self::WithinCapacity => table.try_insert_unique_within_capacity(hash, value, hasher),
        }
    }
}

#[test]
fn insert_within_capacity_full() {
    for insertion in INSERTIONS {
        for requested in [0, 1, 3, 7, 8, 16, 32, 128] {
            let mut table = HashTable::new();
            table.try_reserve(requested, |&value| value).unwrap();
            let capacity = table.capacity();
            let allocation_size = table.allocation_size();
            for value in 0..capacity as u64 {
                let entry = insertion
                    .insert(&mut table, value, value, |_| panic!("unexpected rehash"))
                    .unwrap();
                assert_eq!(*entry.get(), value);
                assert_eq!(table.capacity(), capacity);
                assert_eq!(table.allocation_size(), allocation_size);
            }
            let value = capacity as u64;
            assert_eq!(
                insertion
                    .insert(&mut table, value, value, |_| panic!("unexpected rehash"))
                    .unwrap_err(),
                value
            );
            assert_eq!(table.len(), capacity);
            assert_eq!(table.capacity(), capacity);
            assert_eq!(table.allocation_size(), allocation_size);
            for value in 0..capacity as u64 {
                assert_eq!(table.find(value, |&item| item == value), Some(&value));
            }
        }
    }
}

#[derive(Debug)]
struct DropCounter<'a> {
    value: usize,
    drops: &'a Cell<usize>,
}

impl<'a> DropCounter<'a> {
    fn new(value: usize, drops: &'a Cell<usize>) -> Self {
        Self { value, drops }
    }
}

impl Drop for DropCounter<'_> {
    fn drop(&mut self) {
        self.drops.set(self.drops.get() + 1);
    }
}

#[test]
fn insert_within_capacity_drop() {
    for insertion in INSERTIONS {
        for requested in [0, 1] {
            let drops = Cell::new(0);
            let mut table = HashTable::with_capacity(requested);
            let capacity = table.capacity();
            for value in 0..capacity {
                let mut entry = insertion
                    .insert(&mut table, 0, DropCounter::new(value, &drops), |_| {
                        panic!("unexpected rehash")
                    })
                    .unwrap();
                let updated = value + capacity;
                entry.get_mut().value = updated;
                assert_eq!(
                    table.find(0, |item| item.value == updated).unwrap().value,
                    updated
                );
            }
            let rejected = insertion
                .insert(&mut table, 0, DropCounter::new(usize::MAX, &drops), |_| {
                    panic!("unexpected rehash")
                })
                .unwrap_err();
            assert_eq!(rejected.value, usize::MAX);
            assert_eq!(drops.get(), 0);
            drop(rejected);
            assert_eq!(drops.get(), 1);
            drop(table);
            assert_eq!(drops.get(), capacity + 1);
        }
    }
}

#[test]
fn insert_within_capacity_reuses_tombstone() {
    for insertion in INSERTIONS {
        let mut table = HashTable::with_capacity(32);
        let capacity = table.capacity();
        let allocation_size = table.allocation_size();
        // A single collision chain leaves a tombstone when removing from its middle,
        // rather than an empty bucket which would restore growth capacity.
        for value in 0..capacity {
            insertion
                .insert(&mut table, 0, value, |_| panic!("unexpected rehash"))
                .unwrap();
        }
        let mut removed = 20;
        for replacement in capacity..capacity + 16 {
            let entry = table.find_entry(0, |&value| value == removed).unwrap();
            let removed_index = entry.bucket_index();
            assert_eq!(entry.remove().0, removed);
            assert_eq!(table.len(), capacity - 1);
            assert_eq!(table.capacity(), table.len());
            assert_eq!(table.find(0, |&value| value == removed), None);
            let entry = insertion
                .insert(&mut table, 0, replacement, |_| panic!("unexpected rehash"))
                .unwrap();
            assert_eq!(entry.bucket_index(), removed_index);
            assert_eq!(*entry.get(), replacement);
            assert_eq!(
                table.find(0, |&value| value == replacement),
                Some(&replacement)
            );
            assert_eq!(table.len(), capacity);
            assert_eq!(table.capacity(), capacity);
            assert_eq!(table.allocation_size(), allocation_size);
            assert!(
                insertion
                    .insert(&mut table, 0, usize::MAX, |_| panic!("unexpected rehash"))
                    .is_err()
            );
            removed = replacement;
        }
    }
}

#[test]
fn insert_within_capacity_rehashes_when_needed() {
    // Share a probe sequence but vary fingerprints to check the callback's hashes.
    fn collision_hash(value: usize) -> u64 {
        ((value & 0b1111) as u64) << (usize::BITS - 7)
    }
    for sparse in [false, true] {
        let drops = Cell::new(0);
        let mut table = HashTable::with_capacity(32);
        let capacity = table.capacity();
        let allocation_size = table.allocation_size();
        let buckets = table.num_buckets();
        for value in 0..capacity {
            table
                .try_insert_unique_without_rehash(
                    collision_hash(value),
                    DropCounter::new(value, &drops),
                )
                .unwrap();
        }
        // Pick an empty bucket so strict insertion cannot reuse a tombstone.
        let empty = (0..buckets)
            .find(|&index| table.get_bucket(index).is_none())
            .unwrap();
        let insert_hash = u64::try_from(empty).unwrap();
        let hash = |value| {
            if value == usize::MAX {
                insert_hash
            } else {
                collision_hash(value)
            }
        };
        let removed = if sparse { capacity * 3 / 4 } else { 1 };
        for value in 0..removed {
            table
                .find_entry(hash(value), |item| item.value == value)
                .unwrap()
                .remove();
        }
        assert_eq!(table.len(), capacity - removed);
        assert_eq!(table.capacity(), table.len());
        assert_eq!(table.len() > capacity / 2, !sparse);
        assert_eq!(drops.get(), removed);
        let before: Vec<_> = table.iter().map(|item| item.value).collect();
        let rejected = table
            .try_insert_unique_without_rehash(insert_hash, DropCounter::new(usize::MAX, &drops))
            .unwrap_err();
        assert_eq!(rejected.value, usize::MAX);
        assert_eq!(drops.get(), removed);
        assert_eq!(
            table.iter().map(|item| item.value).collect::<Vec<_>>(),
            before
        );
        assert_eq!(table.len(), before.len());
        assert_eq!(table.capacity(), before.len());
        assert_eq!(table.allocation_size(), allocation_size);

        // Reuse the rejected value: cleanup must not drop it or any surviving entry.
        // Dense cleanup must not follow ordinary insertion's growth heuristic.
        let hashes = Cell::new(0);
        table
            .try_insert_unique_within_capacity(insert_hash, rejected, |item| {
                hashes.set(hashes.get() + 1);
                hash(item.value)
            })
            .unwrap();
        assert!(hashes.get() > 0);
        assert_eq!(drops.get(), removed);
        assert_eq!(table.len(), before.len() + 1);
        assert_eq!(table.capacity(), capacity);
        assert_eq!(table.allocation_size(), allocation_size);
        assert_eq!(table.num_buckets(), buckets);
        for value in before.into_iter().chain([usize::MAX]) {
            assert_eq!(
                table
                    .find(hash(value), |item| item.value == value)
                    .unwrap()
                    .value,
                value
            );
        }
        drop(table);
        assert_eq!(drops.get(), capacity + 1);
    }
}

#[test]
fn insert_within_capacity_zero_sized() {
    for insertion in INSERTIONS {
        let mut table = HashTable::with_capacity(32);
        let capacity = table.capacity();
        let allocation_size = table.allocation_size();
        for _ in 0..capacity {
            insertion
                .insert(&mut table, 0, (), |_| panic!("unexpected rehash"))
                .unwrap();
        }
        assert!(
            insertion
                .insert(&mut table, 0, (), |_| panic!("unexpected rehash"))
                .is_err()
        );
        assert_eq!(table.len(), capacity);
        assert_eq!(table.capacity(), capacity);
        assert_eq!(table.allocation_size(), allocation_size);
    }
}
