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
    clone_small,
    clone_from_small,
    clone_large,
    clone_from_large,
    rehash_in_place
);
criterion_main!(benches);
