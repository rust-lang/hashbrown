// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(test)]

extern crate hashbrown;
extern crate rustc_hash;
extern crate test;
extern crate rand;

use std::hash::Hash;
use test::Bencher;

use hashbrown::HashMap;
use hashbrown::HashSet;
use rand::Rng;
//use rustc_hash::FxHashMap as HashMap;
//use std::collections::HashMap;

fn new_map<K: Eq + Hash, V>() -> HashMap<K, V> {
    HashMap::default()
}

#[bench]
fn new_drop(b: &mut Bencher) {
    b.iter(|| {
        let m: HashMap<i32, i32> = new_map();
        assert_eq!(m.len(), 0);
    })
}

#[bench]
fn new_insert_drop(b: &mut Bencher) {
    b.iter(|| {
        let mut m = new_map();
        m.insert(0, 0);
        assert_eq!(m.len(), 1);
    })
}

#[bench]
fn grow_by_insertion(b: &mut Bencher) {
    let mut m = new_map();

    for i in 1..1001 {
        m.insert(i, i);
    }

    let mut k = 1001;

    b.iter(|| {
        m.insert(k, k);
        k += 1;
    });
}

#[bench]
fn test_insertion_removal(b: &mut Bencher) {
    let mut m: HashSet<Vec<u8>> = HashSet::new();
    let tx: Vec<Vec<u8>> = (0..4096)
             .map(|_| 
                (rand::thread_rng().gen_iter::<u8>().take(16)).collect())
             .collect();

    b.iter(|| {
        for i in 0..4096 {
            assert_eq!(m.contains(&tx[i].clone()), false);
            assert_eq!(m.insert(tx[i].clone()), true);
        }
        for i in 0..4096 {
            println!("removing {} {:?}", i, tx[i]);
            assert_eq!(m.remove(&tx[i]), true);
        }
    });
}


#[bench]
fn find_existing(b: &mut Bencher) {
    let mut m = new_map();

    for i in 1..1001 {
        m.insert(i, i);
    }

    b.iter(|| {
        for i in 1..1001 {
            m.contains_key(&i);
        }
    });
}

#[bench]
fn find_nonexisting(b: &mut Bencher) {
    let mut m = new_map();

    for i in 1..1001 {
        m.insert(i, i);
    }

    b.iter(|| {
        for i in 1001..2001 {
            m.contains_key(&i);
        }
    });
}

#[bench]
fn hashmap_as_queue(b: &mut Bencher) {
    let mut m = new_map();

    for i in 1..1001 {
        m.insert(i, i);
    }

    let mut k = 1;

    b.iter(|| {
        m.remove(&k);
        m.insert(k + 1000, k + 1000);
        k += 1;
    });
}

#[bench]
fn get_remove_insert(b: &mut Bencher) {
    let mut m = new_map();

    for i in 1..1001 {
        m.insert(i, i);
    }

    let mut k = 1;

    b.iter(|| {
        m.get(&(k + 400));
        m.get(&(k + 2000));
        m.remove(&k);
        m.insert(k + 1000, k + 1000);
        k += 1;
    })
}
