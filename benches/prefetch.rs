//! Batch-lookup benchmark: look up a list of keys in a large `HashMap`, with
//! and without software-prefetching a key a few iterations ahead.
//!
//! Prefetching only pays off when the table is large enough that its control
//! bytes spill out of the L2/L3 cache *and* the caller can issue the prefetch
//! far enough ahead of the use. So this benchmark sweeps the table size and
//! uses a randomized lookup order (so the access pattern is cache-hostile).
//! On a small, cache-resident table the prefetch is noise (or a slight loss);
//! the win shows up on the large sizes.

use criterion::{BenchmarkId, Criterion, Throughput};
use hashbrown::{DefaultHashBuilder, HashMap};
use std::hint::black_box;

// 16-byte keys, like a common join-key shape (two u64s).
type Key = (u64, u64);

const SIZES: &[usize] = &[1 << 12, 1 << 16, 1 << 18, 1 << 20, 1 << 22];
const LOOKAHEAD: usize = 8;
const N_QUERIES: usize = 1 << 16;

fn build_map(n: usize) -> HashMap<Key, u64, DefaultHashBuilder> {
    let mut m = HashMap::with_capacity_and_hasher(n, DefaultHashBuilder::default());
    for i in 0..n as u64 {
        m.insert((i, i.wrapping_mul(0x9E37_79B9_7F4A_7C15)), i);
    }
    m
}

// A cheap PRNG so the lookup order is unpredictable to the prefetcher.
fn xorshift(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

fn query_keys(n: usize) -> Vec<Key> {
    let mut state = 0x1234_5678_9ABC_DEF0u64;
    (0..N_QUERIES)
        .map(|_| {
            let i = xorshift(&mut state) % n as u64;
            (i, i.wrapping_mul(0x9E37_79B9_7F4A_7C15))
        })
        .collect()
}

fn lookup_naive(map: &HashMap<Key, u64, DefaultHashBuilder>, keys: &[Key]) -> u64 {
    let mut sum = 0u64;
    for k in keys {
        if let Some(&v) = map.get(k) {
            sum = sum.wrapping_add(v);
        }
    }
    sum
}

fn lookup_prefetched(map: &HashMap<Key, u64, DefaultHashBuilder>, keys: &[Key]) -> u64 {
    let mut sum = 0u64;
    for (i, k) in keys.iter().enumerate() {
        if let Some(next) = keys.get(i + LOOKAHEAD) {
            map.prefetch(next);
        }
        if let Some(&v) = map.get(k) {
            sum = sum.wrapping_add(v);
        }
    }
    sum
}

pub(crate) fn register_benches(c: &mut Criterion) {
    let mut group = c.benchmark_group("batch_lookup");
    group.throughput(Throughput::Elements(N_QUERIES as u64));
    for &n in SIZES {
        let map = build_map(n);
        let keys = query_keys(n);
        group.bench_with_input(BenchmarkId::new("naive", n), &n, |b, _| {
            b.iter(|| black_box(lookup_naive(black_box(&map), black_box(&keys))));
        });
        group.bench_with_input(BenchmarkId::new("prefetch", n), &n, |b, _| {
            b.iter(|| black_box(lookup_prefetched(black_box(&map), black_box(&keys))));
        });
    }
    group.finish();
}
