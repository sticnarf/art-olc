#[cfg(not(target_env = "msvc"))]
use jemallocator::Jemalloc;

#[cfg(not(target_env = "msvc"))]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

use art_olc::Tree;
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use crossbeam_epoch::pin;
use crossbeam_skiplist::SkipMap;
use rand::prelude::*;
use std::{
    collections::{BTreeMap, HashMap},
    fs::File,
    io::{BufRead, BufReader},
};

fn prepare_art(words: &[String]) -> Tree<u32> {
    let map = Tree::new();
    for word in words {
        map.insert(word.as_bytes(), 0, &pin());
    }
    map
}

fn art_get(map: &Tree<u32>, words: &[String]) {
    for word in words {
        black_box(map.get(black_box(word.as_bytes()), &pin()));
    }
}

fn prepare_btree(words: &[String]) -> BTreeMap<String, u32> {
    let mut map = BTreeMap::new();
    for word in words {
        map.insert(word.clone(), 0);
    }
    map
}

fn btree_get(map: &BTreeMap<String, u32>, words: &[String]) {
    for word in words {
        black_box(map.get(black_box(word)));
    }
}

fn prepare_hashmap(words: &[String]) -> HashMap<String, u32> {
    let mut map = HashMap::new();
    for word in words {
        map.insert(word.clone(), 0);
    }
    map
}

fn hashmap_get(map: &HashMap<String, u32>, words: &[String]) {
    for word in words {
        black_box(map.get(black_box(word)));
    }
}

fn prepare_skipmap(words: &[String]) -> SkipMap<String, u32> {
    let map = SkipMap::new();
    for word in words {
        map.insert(word.clone(), 0);
    }
    map
}

fn skipmap_get(map: &SkipMap<String, u32>, words: &[String]) {
    for word in words {
        black_box(map.get(black_box(word)));
    }
}

fn bench_get(c: &mut Criterion) {
    let mut words: Vec<String> = File::open("words.txt")
        .map(BufReader::new)
        .and_then(|f| f.lines().collect())
        .unwrap();
    let mut rng = StdRng::seed_from_u64(114514);
    words.shuffle(&mut rng);

    let mut group = c.benchmark_group("get");
    group.bench_with_input(
        BenchmarkId::new("ART", "single-thread"),
        &words,
        |b, words| {
            let map = prepare_art(words);
            b.iter(|| {
                art_get(&map, words);
            })
        },
    );
    group.bench_with_input(
        BenchmarkId::new("BTreeMap", "single-thread"),
        &words,
        |b, words| {
            let map = prepare_btree(words);
            b.iter(|| {
                btree_get(&map, words);
            })
        },
    );
    group.bench_with_input(
        BenchmarkId::new("HashMap", "single-thread"),
        &words,
        |b, words| {
            let map = prepare_hashmap(words);
            b.iter(|| {
                hashmap_get(&map, words);
            })
        },
    );
    group.bench_with_input(
        BenchmarkId::new("SkipMap", "single-thread"),
        &words,
        |b, words| {
            let map = prepare_skipmap(words);
            b.iter(|| {
                skipmap_get(&map, words);
            })
        },
    );
    group.finish();
}

criterion_group!(benches, bench_get);
criterion_main!(benches);
