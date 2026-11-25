//! Benches for `HashMap::prefetch_get` and `HashMap::prefetch_insert`.
//!
//! Two flavors of workload: batch lookups (`prefetch_get`) and batch inserts
//! (`prefetch_insert`). Each flavor runs against integer keys (`(u64, u64)`)
//! and heap-allocated `String` keys; the string variant exists because
//! heap-allocated keys force a pointer dereference to hash, which changes the
//! cache-miss profile of the prefetch call itself.

use criterion::{BenchmarkId, Criterion, Throughput};
use hashbrown::{DefaultHashBuilder, HashMap};
use std::hint::black_box;

// ---------- Shared knobs ----------
//
// Table-size sweep covers the in-cache → cache-spilled crossover. The prefetch
// is a hint that pays off only when the control bytes have spilled out of L2/L3
// and the caller has independent work to overlap with the fetch, so the small
// sizes are a sanity check (prefetch should be noise or a slight loss) and the
// large sizes are where the win materializes.
const SIZES: &[usize] = &[1 << 12, 1 << 16, 1 << 18, 1 << 20, 1 << 22];

// The number of iterations ahead we issue the prefetch. Eight is a common
// rule-of-thumb (covers ~one cache-miss-worth of work on modern cores) and
// matches the abseil prefetch_hash idiom.
const LOOKAHEAD: usize = 8;

// Query batch size. Large enough that fixed per-iteration overhead is
// amortized; small enough that the bench finishes in seconds.
const N_QUERIES: usize = 1 << 16;

// 16-byte key, like a common join-key shape (two u64s).
type Key = (u64, u64);

// ---------- Integer-key workload ----------
//
// Keys are packed inline (16 bytes), so hashing the key never dereferences
// outside the slice. This isolates the prefetch effect to the table's control
// + data lines: there's no extra cache miss "behind" the key itself.

fn build_map(n: usize) -> HashMap<Key, u64, DefaultHashBuilder> {
    let mut m = HashMap::with_capacity_and_hasher(n, DefaultHashBuilder::default());
    for i in 0..n as u64 {
        m.insert((i, i.wrapping_mul(0x9E37_79B9_7F4A_7C15)), i);
    }
    m
}

// A cheap PRNG so the lookup order is unpredictable to the hardware prefetcher.
// `xorshift` is deterministic given the seed; the same query set is generated
// each invocation so the comparison is apples-to-apples.
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

// Miss-heavy query set: every key is drawn from outside the inserted range so
// every lookup misses. The probe finds an empty control group and never reads
// the data line. This is the regime where `prefetch_get`'s ctrl-only hint is
// supposed to win over `prefetch`-both, because the data prefetch is wasted
// bandwidth when the lookup terminates on the control bytes.
fn query_keys_miss(n: usize) -> Vec<Key> {
    let mut state = 0xCAFE_BABE_DEAD_BEEFu64;
    let offset = (n as u64).saturating_mul(2);
    (0..N_QUERIES)
        .map(|_| {
            let i = offset + (xorshift(&mut state) % n as u64);
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

// The look-ahead pattern: prefetch the key `i + LOOKAHEAD` iterations ahead
// while processing key `i`. By the time iteration `i + LOOKAHEAD` arrives, the
// control line is already in cache.
fn lookup_prefetched(map: &HashMap<Key, u64, DefaultHashBuilder>, keys: &[Key]) -> u64 {
    let mut sum = 0u64;
    for (i, k) in keys.iter().enumerate() {
        if let Some(next) = keys.get(i + LOOKAHEAD) {
            map.prefetch_get(next);
        }
        if let Some(&v) = map.get(k) {
            sum = sum.wrapping_add(v);
        }
    }
    sum
}

// ---------- Heap-string workload ----------
//
// Heap-allocated `String` keys are scattered across allocations: each key is a
// pointer + length, and hashing the key dereferences the pointer to read the
// bytes. That's an extra cache miss "behind" the key compared to the inline
// integer keys. Whether prefetch still wins on this workload depends on how
// much of that extra miss the look-ahead can overlap with the caller's work.
// Note that the prefetch_get call here doesn't hint the key's heap buffer; it
// only hints the control bytes the key's *hash* would land on. The key
// dereference cost is paid at the prefetch site (during `make_hash`), not the
// lookup site.

fn build_map_string(n: usize) -> HashMap<String, u64, DefaultHashBuilder> {
    let mut m = HashMap::with_capacity_and_hasher(n, DefaultHashBuilder::default());
    for i in 0..n as u64 {
        m.insert(
            format!("key-{}-{:016x}", i, i.wrapping_mul(0x9E37_79B9_7F4A_7C15)),
            i,
        );
    }
    m
}

fn query_keys_string(n: usize) -> Vec<String> {
    let mut state = 0x1234_5678_9ABC_DEF0u64;
    (0..N_QUERIES)
        .map(|_| {
            let i = xorshift(&mut state) % n as u64;
            format!("key-{}-{:016x}", i, i.wrapping_mul(0x9E37_79B9_7F4A_7C15))
        })
        .collect()
}

fn lookup_naive_string(map: &HashMap<String, u64, DefaultHashBuilder>, keys: &[&str]) -> u64 {
    let mut sum = 0u64;
    for k in keys {
        if let Some(&v) = map.get(*k) {
            sum = sum.wrapping_add(v);
        }
    }
    sum
}

fn lookup_prefetched_string(map: &HashMap<String, u64, DefaultHashBuilder>, keys: &[&str]) -> u64 {
    let mut sum = 0u64;
    for (i, k) in keys.iter().enumerate() {
        if let Some(next) = keys.get(i + LOOKAHEAD) {
            map.prefetch_get(*next);
        }
        if let Some(&v) = map.get(*k) {
            sum = sum.wrapping_add(v);
        }
    }
    sum
}

// ---------- Insert workload (prefetch_insert) ----------
//
// Inserts hint *both* the control line and the data bucket, since an insert
// will write to the data position regardless of whether the slot is currently
// empty. The bench reserves capacity up front so the workload measures the
// steady-state insert (find-empty-slot + write), not amortized growth.

fn insert_naive(keys: &[Key], capacity: usize) -> u64 {
    let mut m: HashMap<Key, u64, DefaultHashBuilder> =
        HashMap::with_capacity_and_hasher(capacity, DefaultHashBuilder::default());
    let mut sum = 0u64;
    for (i, &k) in keys.iter().enumerate() {
        m.insert(k, i as u64);
        sum = sum.wrapping_add(i as u64);
    }
    sum
}

fn insert_prefetched(keys: &[Key], capacity: usize) -> u64 {
    let mut m: HashMap<Key, u64, DefaultHashBuilder> =
        HashMap::with_capacity_and_hasher(capacity, DefaultHashBuilder::default());
    let mut sum = 0u64;
    for (i, &k) in keys.iter().enumerate() {
        if let Some(next) = keys.get(i + LOOKAHEAD) {
            m.prefetch_insert(next);
        }
        m.insert(k, i as u64);
        sum = sum.wrapping_add(i as u64);
    }
    sum
}

// Unique-insert key set: every key is distinct so each iteration adds a fresh
// entry. Capacity is reserved up front (in the bench harness) so the workload
// doesn't include rehash cost.
fn insert_keys(n: usize) -> Vec<Key> {
    let mut state = 0xDEAD_BEEF_FACE_CAFEu64;
    (0..n)
        .map(|_| {
            let i = xorshift(&mut state);
            (i, i.wrapping_mul(0x9E37_79B9_7F4A_7C15))
        })
        .collect()
}

// ---------- Bench registration ----------

pub(crate) fn register_benches(c: &mut Criterion) {
    // Group 1: integer-key batch lookup, queries hit the map (100% hit rate).
    // Probes find a matching tag and read the data line on every iteration, so
    // prefetching the data line is useful. This is the regime where the
    // original `prefetch` (hint both ctrl + data) is expected to win and a
    // ctrl-only `prefetch_get` is expected to lose.
    let mut group = c.benchmark_group("batch_lookup");
    group.throughput(Throughput::Elements(N_QUERIES as u64));
    for &n in SIZES {
        let map = build_map(n);
        let keys = query_keys(n);
        group.bench_with_input(BenchmarkId::new("naive", n), &n, |b, _| {
            b.iter(|| black_box(lookup_naive(black_box(&map), black_box(&keys))));
        });
        group.bench_with_input(BenchmarkId::new("prefetch_get", n), &n, |b, _| {
            b.iter(|| black_box(lookup_prefetched(black_box(&map), black_box(&keys))));
        });
    }
    group.finish();

    // Group 1b: integer-key batch lookup, queries miss the map (0% hit rate).
    // Probes find an empty control group and never read the data line, so the
    // data prefetch in `prefetch`-both would be wasted bandwidth. This is the
    // regime where ctrl-only `prefetch_get` is expected to win, because the
    // ctrl hint is still useful and the wasted data hint is avoided.
    let mut group = c.benchmark_group("batch_lookup_miss");
    group.throughput(Throughput::Elements(N_QUERIES as u64));
    for &n in SIZES {
        let map = build_map(n);
        let keys = query_keys_miss(n);
        group.bench_with_input(BenchmarkId::new("naive", n), &n, |b, _| {
            b.iter(|| black_box(lookup_naive(black_box(&map), black_box(&keys))));
        });
        group.bench_with_input(BenchmarkId::new("prefetch_get", n), &n, |b, _| {
            b.iter(|| black_box(lookup_prefetched(black_box(&map), black_box(&keys))));
        });
    }
    group.finish();

    // Group 2: heap-string-key batch lookup (prefetch_get). String keys force a
    // pointer dereference at hash time, exposing whether the prefetch's
    // look-ahead overlap survives the extra cache miss on the key buffer.
    let mut group = c.benchmark_group("batch_lookup_string");
    group.throughput(Throughput::Elements(N_QUERIES as u64));
    for &n in SIZES {
        let map = build_map_string(n);
        let keys = query_keys_string(n);
        let key_refs: Vec<&str> = keys.iter().map(String::as_str).collect();
        group.bench_with_input(BenchmarkId::new("naive", n), &n, |b, _| {
            b.iter(|| black_box(lookup_naive_string(black_box(&map), black_box(&key_refs))));
        });
        group.bench_with_input(BenchmarkId::new("prefetch_get", n), &n, |b, _| {
            b.iter(|| {
                black_box(lookup_prefetched_string(
                    black_box(&map),
                    black_box(&key_refs),
                ))
            });
        });
    }
    group.finish();

    // Group 3: integer-key batch insert (prefetch_insert). Capacity is reserved
    // so the bench measures steady-state insert cost (find-empty-slot + write),
    // not amortized growth.
    let mut group = c.benchmark_group("batch_insert");
    group.throughput(Throughput::Elements(N_QUERIES as u64));
    for &n in SIZES {
        let keys = insert_keys(N_QUERIES);
        let capacity = n;
        group.bench_with_input(BenchmarkId::new("naive", n), &n, |b, _| {
            b.iter(|| black_box(insert_naive(black_box(&keys), capacity)));
        });
        group.bench_with_input(BenchmarkId::new("prefetch_insert", n), &n, |b, _| {
            b.iter(|| black_box(insert_prefetched(black_box(&keys), capacity)));
        });
    }
    group.finish();
}
