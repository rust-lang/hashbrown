// This file contains all the benchmarks from `hashbrown`.
// To bench, `hashbrown` use a crates called `criterion`.

mod bench_util;

use crate::bench_util::DropType;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use hashbrown::{HashMap, HashSet};

fn clone_small(c: &mut Criterion) {
    let mut m = HashMap::new();
    for i in 0..10 {
        m.insert(i, DropType(i));
    }

    c.bench_function("clone_small", |b| {
        b.iter(|| {
            black_box(m.clone());
        })
    });
}

fn clone_from_small(c: &mut Criterion) {
    let mut m = HashMap::new();
    let mut m2 = HashMap::new();
    for i in 0..10 {
        m.insert(i, DropType(i));
    }

    c.bench_function("clone_from_small", |b| {
        b.iter(|| {
            m2.clone_from(&m);
            black_box(&mut m2);
        })
    });
}

fn clone_large(c: &mut Criterion) {
    let mut m = HashMap::new();
    for i in 0..1000 {
        m.insert(i, DropType(i));
    }

    c.bench_function("clone_large", |b| {
        b.iter(|| {
            black_box(m.clone());
        })
    });
}

fn clone_from_large(c: &mut Criterion) {
    let mut m = HashMap::new();
    let mut m2 = HashMap::new();
    for i in 0..1000 {
        m.insert(i, DropType(i));
    }

    c.bench_function("clone_from_large", |b| {
        b.iter(|| {
            m2.clone_from(&m);
            black_box(&mut m2);
        })
    });
}

fn rehash_in_place(c: &mut Criterion) {
    c.bench_function("rehash_in_place", |b| {
        b.iter(|| {
            let mut set = HashSet::new();

            // Each loop triggers one rehash
            for _ in 0..10 {
                for i in 0..224 {
                    set.insert(i);
                }

                assert_eq!(
                    set.capacity(),
                    224,
                    "The set must be at or close to capacity to trigger a re hashing"
                );

                for i in 100..1400 {
                    set.remove(&(i - 100));
                    set.insert(i);
                }
                set.clear();
            }
        })
    });
}

criterion_group!(
    benches,
    // hashbrown
    clone_small,
    clone_from_small,
    clone_large,
    clone_from_large,
    rehash_in_place,
    // other
    insert_ahash_serial,
    insert_std_serial,
    insert_ahash_highbits,
    insert_std_highbits,
    insert_ahash_random,
    insert_std_random,
    grow_insert_ahash_serial,
    grow_insert_std_serial,
    grow_insert_ahash_highbits,
    grow_insert_std_highbits,
    grow_insert_ahash_random,
    grow_insert_std_random,
    insert_erase_ahash_serial,
    insert_erase_std_serial,
    insert_erase_ahash_highbits,
    insert_erase_std_highbits,
    insert_erase_ahash_random,
    insert_erase_std_random,
    lookup_ahash_serial,
    lookup_std_serial,
    lookup_ahash_highbits,
    lookup_std_highbits,
    lookup_ahash_random,
    lookup_std_random,
    lookup_fail_ahash_serial,
    lookup_fail_std_serial,
    lookup_fail_ahash_highbits,
    lookup_fail_std_highbits,
    lookup_fail_ahash_random,
    lookup_fail_std_random,
    iter_ahash_serial,
    iter_std_serial,
    iter_ahash_highbits,
    iter_std_highbits,
    iter_ahash_random,
    iter_std_random
);
criterion_main!(benches);
