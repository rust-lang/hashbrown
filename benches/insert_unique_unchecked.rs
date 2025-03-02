//! Compare `insert` and `insert_unique_unchecked` operations performance.

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use hashbrown::HashMap;

fn insert_benchmark(c: &mut Criterion) {
    let keys: Vec<String> = (0..1000).map(|i| format!("xxxx{}yyyy", i)).collect();
    c.bench_function("insert", |b| {
        b.iter(|| {
            let mut m = HashMap::with_capacity(1000);
            for k in &keys {
                m.insert(black_box(k), black_box(k));
            }
            m
        });
    });
}

fn insert_unique_unchecked_benchmark(c: &mut Criterion) {
    let keys: Vec<String> = (0..1000).map(|i| format!("xxxx{}yyyy", i)).collect();
    c.bench_function("insert_unique_unchecked", |b| {
        b.iter(|| {
            let mut m = HashMap::with_capacity(1000);
            for k in &keys {
                unsafe {
                    m.insert_unique_unchecked(black_box(k), black_box(k));
                }
            }
            m
        });
    });
}

criterion_group!(benches, insert_benchmark, insert_unique_unchecked_benchmark);
criterion_main!(benches);
