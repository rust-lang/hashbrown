//! Compares look-up performance in a "hollowed out" hash-map.
//!
//! The layout of a Swiss Map leads to a number of potential cache-misses:
//!
//! -   The hash-map itself is assumed to be in cache, in a hot loop.
//! -   The control block is accessed based on the low-bits of the hash (hash % number of buckets), which may be a
//!     cache miss.
//! -   The element is accessed _within its group_, based on the control-block check, which may be a cache miss.
//!
//! Note that the elements within a group are NOT necessarily laid out contiguously. The presence of holes leads to a
//! Swiss Cheese pattern where cache lines contain a mix of elements & uninitialized memory.
//!
//! This benchmark suite attempts to quantify the effect that such a Swiss Cheese pattern may have on performance.

#![feature(test)]

extern crate test;

use test::Bencher;

use hashbrown::HashMap;

use std::{
    hash::{BuildHasher, Hasher},
    mem,
};

//  The cache sizes, for a typical x64 CPU.
//  const L3_CACHE_SIZE: usize = 16 * 1024 * 1024;
const L2_CACHE_SIZE: usize = 512 * 1024;
//  const L1_CACHE_SIZE: usize = 32 * 1024;

//  The number of elements in a group.
//
//  This assumes SSE2.
const GROUP_WIDTH: usize = 16;

//  The experiment requires precisely controlling which group an element ends up in. Using identity allows that easily.
#[derive(Default)]
struct IdentityBuildHasher;

impl BuildHasher for IdentityBuildHasher {
    type Hasher = IdentityHasher;

    fn build_hasher(&self) -> Self::Hasher {
        IdentityHasher::default()
    }
}

#[derive(Default)]
struct IdentityHasher(u64);

impl Hasher for IdentityHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, _bytes: &[u8]) {
        unreachable!("The experiment only uses u64");
    }

    fn write_u64(&mut self, i: u64) {
        self.0 = i;
    }
}

//  The experiment requires precisely controlling the group an element ends up in, so our key will control that.
#[derive(Clone, Copy, Eq, Hash, PartialEq)]
struct Key(u64);

impl Key {
    //  Constructs a new key with:
    //
    //  -   `residual` placed in the top 7 bits -- its high bit should be 0.
    //  -   `differentiator` placed right after residual, allowing making elements non-equal, even if their hashes are.
    //  -   `group` placed in the lower 32 bits.
    fn new(residual: u8, differentiator: u8, group: u32) -> Self {
        let residual = (residual as u64) << 57;
        let differentiator = (differentiator as u64) << 49;
        let group = group as u64;

        Self(residual | differentiator | group)
    }
}

//  The experiment requires precisely controlling the size of the element, to judge cache lines, so we'll use a flexible
//  value type.
#[derive(Clone, Copy)]
struct Value<const N: usize>([u64; N]);

impl<const N: usize> Value<N> {
    //  A function which forces accesses to the content of the value, since looked-up values are typically accessed.
    //
    //  The last byte of the value is accessed, as it is the most distant from the key, and thus the most likely to
    //  cause a cache miss.
    fn last(&self) -> u64 {
        self.0[N - 1]
    }
}

impl<const N: usize> Default for Value<N> {
    fn default() -> Self {
        Self([0; N])
    }
}

//  A small value, taking the minimum amount of space and _stilL_ carrying some state.
const QUARTER_VALUE: usize = 1;

//  A value calibrated so that (Key, Value) takes exactly 48 bytes, like (String, String) would, or 3/4 of a cache line.
const THREE_QUARTERS_VALUE: usize = 5;

//  A value calibrated so that (Key, Value) takes a full 64 bytes, or one full cache line.
const SINGLE_VALUE: usize = 7;

//  A value calibrated so that (Key, Value) takes a full 128 bytes, or two full cache lines.
const DOUBLE_VALUE: usize = 15;

//  Full residuals.
const UNIQUE_RESIDUALS: [u8; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];

//  Our "victim".
type Victim<const N: usize> = HashMap<Key, Value<N>, IdentityBuildHasher>;

//  The experiment requires precisely controlling our keys, the generator will be used to ensure they end up where we
//  need them.
struct VictimGenerator<const N: usize> {
    //  The number of groups we'll fill in.
    //
    //  Note that only even groups are filled, so the capacity of the map will be 2 * GROUP_WIDTH * number_groups.
    number_groups: usize,
    //  The residuals & differentiators we'll use within a group, each one corresponding to one element.
    number_controls: usize,
    controls: [(u8, u8); GROUP_WIDTH],
}

impl<const N: usize> VictimGenerator<N> {
    //  Creates a new generator, according to specifications.
    //
    //  -   `size`: the size _in cache_ of the elements array.
    //  -   `residuals`: array of residuals to use for each group, indirectly controls the number of elements per group.
    fn new<R>(size: usize, residuals: R) -> Self
    where
        R: IntoIterator<Item = u8>,
    {
        Self::with_differentiators(size, residuals, std::iter::repeat(0u8))
    }

    //  Creates a new generator, according to specifications.
    //
    //  -   `size`: the size _in cache_ of the elements array.
    //  -   `residuals`: residuals to use for each group, indirectly controls the number of elements per group.
    //  -   `differentiators`: differentiators to use for each group.
    fn with_differentiators<R, D>(size: usize, residuals: R, differentiators: D) -> Self
    where
        R: IntoIterator<Item = u8>,
        D: IntoIterator<Item = u8>,
    {
        let number_elements = size / mem::size_of::<(Key, Value<N>)>();

        let number_groups = number_elements / GROUP_WIDTH / 2;

        let mut number_controls = 0;
        let mut controls = [(0u8, 0u8); GROUP_WIDTH];

        for (residual, differentiator) in residuals.into_iter().zip(differentiators) {
            controls[number_controls] = (residual, differentiator);
            number_controls += 1;
        }

        Self {
            number_groups,
            number_controls,
            controls,
        }
    }

    //  Creates an empty victim.
    fn spawn_empty(&self) -> Victim<N> {
        let capacity = self.number_groups * GROUP_WIDTH * 2;

        Victim::with_capacity_and_hasher(capacity, IdentityBuildHasher)
    }

    //  Creates a new victim, full for now.
    fn spawn(&self) -> Victim<N> {
        let mut victim = self.spawn_empty();

        victim.extend(self.keys().map(|key| (key, Value::default())));

        victim
    }

    //  Hollows out a victim, returning which controls are _still_ present.
    //
    //  The specified number of `holes` is removed, evenly spread across the residuals specified.
    fn hollow(&self, holes: usize, victim: &mut Victim<N>) -> Vec<(u8, u8)> {
        assert!(
            holes < self.number_controls,
            "To create an empty map, just call `spawn_empty`"
        );

        let holes = Self::compute_holes(holes, self.controls());

        self.keys_with(&holes).for_each(|key| {
            victim.remove(&key);
        });

        self.controls()
            .iter()
            .filter(|control| !holes.contains(control))
            .copied()
            .collect()
    }

    //  Returns an iterator over all the keys of the generator.
    //
    //  The keys are produced _in order_, which is cache friendly, so ideal for insertion but not for benchmarking
    //  look-ups.
    fn keys(&self) -> impl Iterator<Item = Key> + '_ {
        self.keys_with(self.controls())
    }

    //  Returns an iterator over all the keys, as per the specified controls.
    //
    //  The keys are produced _in order_, which is cache friendly, so ideal for insertion but not for benchmarking
    //  look-ups.
    fn keys_with<'a>(&'a self, controls: &'a [(u8, u8)]) -> impl Iterator<Item = Key> + 'a {
        self.groups().flat_map(|g| {
            controls
                .iter()
                .copied()
                .map(move |(r, d)| Key::new(r, d, g))
        })
    }

    //  Returns an iterator over all the keys, as per the specified controls.
    //
    //  The keys are produced in a "clustered" fashion, with half the keys falling close to their predecessor, and the
    //  other half falling further.
    fn clustered_keys(&self) -> impl Iterator<Item = Key> + '_ {
        self.clustered_keys_with(self.controls())
    }

    //  Returns an iterator over all the keys, as per the specified controls.
    //
    //  The keys are produced in a "clustered" fashion, with half the keys falling close to their predecessor, and the
    //  other half falling further.
    fn clustered_keys_with<'a>(
        &'a self,
        controls: &'a [(u8, u8)],
    ) -> impl Iterator<Item = Key> + 'a {
        //  A modern Intel x64 pre-fetches cache lines two a time, or 128 bytes by 128 bytes.
        //
        //  With groups of 16 elements, and groups being separated by an empty group, two elements in "consecutive"
        //  groups are at least 16 elements apart, or 128 bytes apart with 8 bytes elements, so all it takes to
        //  "foil" pre-fetching is to iterate over groups in the inner loop.
        //
        //  On the other hand, consecutive controls (same chunk), should be close to each others, and potentially on the
        //  same cache line, depending on the size of the elements.

        controls.chunks(2).flat_map(|chunk| {
            chunk.iter().copied().flat_map(|(r, d)| {
                self.groups()
                    .map(move |g| test::black_box(Key::new(r, d, g)))
            })
        })
    }

    //  Returns an iterator over all the keys, as per the specified controls.
    //
    //  The keys are produced in a "random" fashion, which is NOT cache friendly, so ideal for benchmarking look-ups.
    fn randomized_keys(&self) -> impl Iterator<Item = Key> + '_ {
        self.randomized_keys_with(self.controls())
    }

    //  Returns an iterator over all the keys, as per the specified controls.
    //
    //  The keys are produced in a "random" fashion, which is NOT cache friendly, so ideal for benchmarking look-ups.
    fn randomized_keys_with<'a>(
        &'a self,
        controls: &'a [(u8, u8)],
    ) -> impl Iterator<Item = Key> + 'a {
        //  A modern Intel x64 pre-fetches cache lines two a time, or 128 bytes by 128 bytes.
        //
        //  With groups of 16 elements, and groups being separated by an empty group, two elements in "consecutive"
        //  groups are at least 16 elements apart, or 128 bytes apart with 8 bytes elements, so all it takes to
        //  "foil" pre-fetching is to iterate over groups in the inner loop.

        controls.iter().copied().flat_map(|(r, d)| {
            self.groups()
                .map(move |g| test::black_box(Key::new(r, d, g)))
        })
    }

    //  Returns an iterator over the groups the generator will use.
    fn groups(&self) -> impl Iterator<Item = u32> + '_ {
        (0..self.number_groups).map(|group| (group as u32) * 2)
    }

    //  Returns the controls (residual + differentiator) the generator will use.
    fn controls(&self) -> &[(u8, u8)] {
        &self.controls[0..self.number_controls]
    }

    //  Computes which residuals to hollow, recursively.
    fn compute_holes(holes: usize, controls: &[(u8, u8)]) -> Vec<(u8, u8)> {
        fn recursive_hollow(holes: usize, controls: &[(u8, u8)], result: &mut Vec<(u8, u8)>) {
            match controls.len() {
                0 => (),
                1 => {
                    if holes > 0 {
                        assert_eq!(1, holes);

                        result.push(controls[0]);
                    }
                }
                _ => {
                    let left_holes = holes / 2;
                    let right_holes = holes - left_holes;

                    let (left_controls, right_controls) = controls.split_at(controls.len() / 2);

                    let before = result.len();

                    recursive_hollow(left_holes, left_controls, result);
                    recursive_hollow(right_holes, right_controls, result);

                    assert_eq!(holes, result.len() - before);
                }
            }
        }

        let mut result = Vec::with_capacity(holes);

        recursive_hollow(holes, controls, &mut result);

        assert_eq!(holes, result.len());

        result
    }
}

macro_rules! bench_suite {
    ($function:ident, $bench_quarter:ident, $bench_three_quarters:ident, $bench_single:ident, $bench_double:ident) => {
        #[bench]
        fn $bench_quarter(b: &mut Bencher) {
            $function::<QUARTER_VALUE>(b);
        }

        #[bench]
        fn $bench_three_quarters(b: &mut Bencher) {
            $function::<THREE_QUARTERS_VALUE>(b);
        }

        #[bench]
        fn $bench_single(b: &mut Bencher) {
            $function::<SINGLE_VALUE>(b);
        }

        #[bench]
        fn $bench_double(b: &mut Bencher) {
            $function::<DOUBLE_VALUE>(b);
        }
    };
}

//  Empty baseline.
//
//  In this scenario, no element is actually inserted, then random look-ups are performed.
//
//  This scenario thus exercises the cache density of the _residuals_.
bench_suite!(
    empty_random_l2,
    swiss_cheese_empty_random_l2_quarter,
    swiss_cheese_empty_random_l2_three_quarters,
    swiss_cheese_empty_random_l2_single,
    swiss_cheese_empty_random_l2_double
);

fn empty_random_l2<const N: usize>(b: &mut Bencher) {
    let generator = VictimGenerator::<N>::new(L2_CACHE_SIZE * 16, UNIQUE_RESIDUALS);
    let victim = generator.spawn_empty();

    let mut witness = 0;

    b.iter(|| {
        generator.randomized_keys().for_each(|key| {
            if let Some(value) = victim.get(&key) {
                witness += value.last();
            }
        })
    });

    assert_eq!(0, witness);
}

//  Full baseline.
//
//  In this scenario, all "expected" keys are inserted, then random look-ups are performed.
//
//  This scenario thus exercises the cache density of the _elements_ themselves.
bench_suite!(
    full_random_l2,
    swiss_cheese_full_random_l2_quarter,
    swiss_cheese_full_random_l2_three_quarters,
    swiss_cheese_full_random_l2_single,
    swiss_cheese_full_random_l2_double
);

fn full_random_l2<const N: usize>(b: &mut Bencher) {
    let generator = VictimGenerator::<N>::new(L2_CACHE_SIZE * 16, UNIQUE_RESIDUALS);
    let victim = generator.spawn();

    let mut witness = 0;

    b.iter(|| {
        generator.randomized_keys().for_each(|key| {
            if let Some(value) = victim.get(&key) {
                witness += value.last();
            }
        })
    });

    assert_eq!(0, witness);
}

//  Half benchmark.
//
//  In this scenario, all keys are inserted _then_ half of them are removed. Then random look-ups are performed on the
//  still present keys.
//
//  This scenario exercises the cache density of the elements after holes are poked.
bench_suite!(
    half_random_l2,
    swiss_cheese_half_random_l2_quarter,
    swiss_cheese_half_random_l2_three_quarters,
    swiss_cheese_half_random_l2_single,
    swiss_cheese_half_random_l2_double
);

fn half_random_l2<const N: usize>(b: &mut Bencher) {
    let generator = VictimGenerator::<N>::new(L2_CACHE_SIZE * 16, UNIQUE_RESIDUALS);

    let (victim, controls) = {
        let mut victim = generator.spawn();
        let controls = generator.hollow(UNIQUE_RESIDUALS.len() / 2, &mut victim);

        (victim, controls)
    };

    let mut witness = 0;

    b.iter(|| {
        generator.randomized_keys_with(&controls).for_each(|key| {
            if let Some(value) = victim.get(&key) {
                witness += value.last();
            }
        })
    });

    assert_eq!(0, witness);
}

//  Quarter benchmark.
//
//  In this scenario, all keys are inserted _then_ 3/4 of them are removed. Then random look-ups are performed on the
//  still present keys.
//
//  This scenario exercises the cache density of the elements after many holes are poked.
bench_suite!(
    quarter_random_l2,
    swiss_cheese_quarter_random_l2_quarter,
    swiss_cheese_quarter_random_l2_three_quarters,
    swiss_cheese_quarter_random_l2_single,
    swiss_cheese_quarter_random_l2_double
);

fn quarter_random_l2<const N: usize>(b: &mut Bencher) {
    let generator = VictimGenerator::<N>::new(L2_CACHE_SIZE * 16, UNIQUE_RESIDUALS);

    let (victim, controls) = {
        let mut victim = generator.spawn();
        let controls = generator.hollow(UNIQUE_RESIDUALS.len() * 3 / 4, &mut victim);

        (victim, controls)
    };

    let mut witness = 0;

    b.iter(|| {
        generator.randomized_keys_with(&controls).for_each(|key| {
            if let Some(value) = victim.get(&key) {
                witness += value.last();
            }
        })
    });

    assert_eq!(0, witness);
}

//  Eighth benchmark.
//
//  In this scenario, all keys are inserted _then_ 7/8 of them are removed. Then random look-ups are performed on the
//  still present keys.
//
//  This scenario exercises the cache density of the elements after many holes are poked.
bench_suite!(
    eigth_random_l2,
    swiss_cheese_eigth_random_l2_quarter,
    swiss_cheese_eigth_random_l2_three_quarters,
    swiss_cheese_eigth_random_l2_single,
    swiss_cheese_eigth_random_l2_double
);

fn eigth_random_l2<const N: usize>(b: &mut Bencher) {
    let generator = VictimGenerator::<N>::new(L2_CACHE_SIZE * 16, UNIQUE_RESIDUALS);

    let (victim, controls) = {
        let mut victim = generator.spawn();
        let controls = generator.hollow(UNIQUE_RESIDUALS.len() * 7 / 8, &mut victim);

        (victim, controls)
    };

    let mut witness = 0;

    b.iter(|| {
        generator.randomized_keys_with(&controls).for_each(|key| {
            if let Some(value) = victim.get(&key) {
                witness += value.last();
            }
        })
    });

    assert_eq!(0, witness);
}

//  Lone benchmark.
//
//  In this scenario, all keys are inserted _then_ all but one of them are removed. Then random look-ups are performed on
//  the still present keys.
//
//  This scenario exercises the cache density of the elements after many holes are poked.
bench_suite!(
    lone_random_l2,
    swiss_cheese_lone_random_l2_quarter,
    swiss_cheese_lone_random_l2_three_quarters,
    swiss_cheese_lone_random_l2_single,
    swiss_cheese_lone_random_l2_double
);

fn lone_random_l2<const N: usize>(b: &mut Bencher) {
    let generator = VictimGenerator::<N>::new(L2_CACHE_SIZE * 16, UNIQUE_RESIDUALS);

    let (victim, controls) = {
        let mut victim = generator.spawn();
        let controls = generator.hollow(UNIQUE_RESIDUALS.len() - 1, &mut victim);

        (victim, controls)
    };

    let mut witness = 0;

    b.iter(|| {
        generator.randomized_keys_with(&controls).for_each(|key| {
            if let Some(value) = victim.get(&key) {
                witness += value.last();
            }
        })
    });

    assert_eq!(0, witness);
}

//  Empty baseline.
//
//  In this scenario, no element is actually inserted, then clustered look-ups are performed.
//
//  This scenario thus exercises the cache density of the _residuals_.
bench_suite!(
    empty_cluster_l2,
    swiss_cheese_empty_cluster_l2_quarter,
    swiss_cheese_empty_cluster_l2_three_quarters,
    swiss_cheese_empty_cluster_l2_single,
    swiss_cheese_empty_cluster_l2_double
);

fn empty_cluster_l2<const N: usize>(b: &mut Bencher) {
    let generator = VictimGenerator::<N>::new(L2_CACHE_SIZE * 16, UNIQUE_RESIDUALS);
    let victim = generator.spawn_empty();

    let mut witness = 0;

    b.iter(|| {
        generator.clustered_keys().for_each(|key| {
            if let Some(value) = victim.get(&key) {
                witness += value.last();
            }
        })
    });

    assert_eq!(0, witness);
}

//  Full baseline.
//
//  In this scenario, all "expected" keys are inserted, then clustered look-ups are performed.
//
//  This scenario thus exercises the cache density of the _elements_ themselves.
bench_suite!(
    full_cluster_l2,
    swiss_cheese_full_cluster_l2_quarter,
    swiss_cheese_full_cluster_l2_three_quarters,
    swiss_cheese_full_cluster_l2_single,
    swiss_cheese_full_cluster_l2_double
);

fn full_cluster_l2<const N: usize>(b: &mut Bencher) {
    let generator = VictimGenerator::<N>::new(L2_CACHE_SIZE * 16, UNIQUE_RESIDUALS);
    let victim = generator.spawn();

    let mut witness = 0;

    b.iter(|| {
        generator.clustered_keys().for_each(|key| {
            if let Some(value) = victim.get(&key) {
                witness += value.last();
            }
        })
    });

    assert_eq!(0, witness);
}

//  Half benchmark.
//
//  In this scenario, all keys are inserted _then_ half of them are removed. Then clustered look-ups are performed on
//  the still present keys.
//
//  This scenario exercises the cache density of the elements after holes are poked.
bench_suite!(
    half_cluster_l2,
    swiss_cheese_half_cluster_l2_quarter,
    swiss_cheese_half_cluster_l2_three_quarters,
    swiss_cheese_half_cluster_l2_single,
    swiss_cheese_half_cluster_l2_double
);

fn half_cluster_l2<const N: usize>(b: &mut Bencher) {
    let generator = VictimGenerator::<N>::new(L2_CACHE_SIZE * 16, UNIQUE_RESIDUALS);

    let (victim, controls) = {
        let mut victim = generator.spawn();
        let controls = generator.hollow(UNIQUE_RESIDUALS.len() / 2, &mut victim);

        (victim, controls)
    };

    let mut witness = 0;

    b.iter(|| {
        generator.randomized_keys_with(&controls).for_each(|key| {
            if let Some(value) = victim.get(&key) {
                witness += value.last();
            }
        })
    });

    assert_eq!(0, witness);
}

//  Quarter benchmark.
//
//  In this scenario, all keys are inserted _then_ 3/4 of them are removed. Then clustered look-ups are performed on the
//  still present keys.
//
//  This scenario exercises the cache density of the elements after many holes are poked.
bench_suite!(
    quarter_cluster_l2,
    swiss_cheese_quarter_cluster_l2_quarter,
    swiss_cheese_quarter_cluster_l2_three_quarters,
    swiss_cheese_quarter_cluster_l2_single,
    swiss_cheese_quarter_cluster_l2_double
);

fn quarter_cluster_l2<const N: usize>(b: &mut Bencher) {
    let generator = VictimGenerator::<N>::new(L2_CACHE_SIZE * 16, UNIQUE_RESIDUALS);

    let (victim, controls) = {
        let mut victim = generator.spawn();
        let controls = generator.hollow(UNIQUE_RESIDUALS.len() * 3 / 4, &mut victim);

        (victim, controls)
    };

    let mut witness = 0;

    b.iter(|| {
        generator.clustered_keys_with(&controls).for_each(|key| {
            if let Some(value) = victim.get(&key) {
                witness += value.last();
            }
        })
    });

    assert_eq!(0, witness);
}

//  Eighth benchmark.
//
//  In this scenario, all keys are inserted _then_ 7/8 of them are removed. Then clustered look-ups are performed on the
//  still present keys.
//
//  This scenario exercises the cache density of the elements after many holes are poked.
bench_suite!(
    eigth_cluster_l2,
    swiss_cheese_eigth_cluster_l2_quarter,
    swiss_cheese_eigth_cluster_l2_three_quarters,
    swiss_cheese_eigth_cluster_l2_single,
    swiss_cheese_eigth_cluster_l2_double
);

fn eigth_cluster_l2<const N: usize>(b: &mut Bencher) {
    let generator = VictimGenerator::<N>::new(L2_CACHE_SIZE * 16, UNIQUE_RESIDUALS);

    let (victim, controls) = {
        let mut victim = generator.spawn();
        let controls = generator.hollow(UNIQUE_RESIDUALS.len() * 7 / 8, &mut victim);

        (victim, controls)
    };

    let mut witness = 0;

    b.iter(|| {
        generator.clustered_keys_with(&controls).for_each(|key| {
            if let Some(value) = victim.get(&key) {
                witness += value.last();
            }
        })
    });

    assert_eq!(0, witness);
}

//  Lone benchmark.
//
//  In this scenario, all keys are inserted _then_ all but one of them are removed. Then clustered look-ups are
//  performed on the still present keys.
//
//  This scenario exercises the cache density of the elements after many holes are poked.
//
//  Furthermore, since there should be no cluster, any performance difference with its "random" counterpart is expected
//  to boil down to key space iteration overhead.
bench_suite!(
    lone_cluster_l2,
    swiss_cheese_lone_cluster_l2_quarter,
    swiss_cheese_lone_cluster_l2_three_quarters,
    swiss_cheese_lone_cluster_l2_single,
    swiss_cheese_lone_cluster_l2_double
);

fn lone_cluster_l2<const N: usize>(b: &mut Bencher) {
    let generator = VictimGenerator::<N>::new(L2_CACHE_SIZE * 16, UNIQUE_RESIDUALS);

    let (victim, controls) = {
        let mut victim = generator.spawn();
        let controls = generator.hollow(UNIQUE_RESIDUALS.len() - 1, &mut victim);

        (victim, controls)
    };

    let mut witness = 0;

    b.iter(|| {
        generator.randomized_keys_with(&controls).for_each(|key| {
            if let Some(value) = victim.get(&key) {
                witness += value.last();
            }
        })
    });

    assert_eq!(0, witness);
}
