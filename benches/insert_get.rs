#[cfg(not(target_env = "msvc"))]
use jemallocator::Jemalloc;

#[cfg(not(target_env = "msvc"))]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

use art_olc::Tree;
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use crossbeam_epoch::pin;
use crossbeam_skiplist::SkipMap;
use crossbeam_utils::thread;
use rand::prelude::*;
use std::{
    collections::BTreeMap,
    fs::File,
    io::{BufRead, BufReader},
    sync::RwLock,
};

const INSERT_THREADS: usize = 4;
const GET_THREADS: usize = 4;

fn prepare_art(words: &[String]) -> Tree<u32> {
    let map = Tree::new();
    for word in words {
        map.insert(word.as_bytes(), 0, &pin());
    }
    map
}

fn art_insert_get(map: &Tree<u32>, words: &[String]) {
    thread::scope(|s| {
        for i in 0..INSERT_THREADS {
            s.spawn(move |_| {
                let words = words
                    .iter()
                    .chain(words.iter())
                    .skip(i * words.len() / INSERT_THREADS)
                    .take(words.len());
                for word in words {
                    map.insert(word.as_bytes(), i as u32, &pin());
                }
            });
        }
        for _ in 0..GET_THREADS {
            s.spawn(|_| {
                for word in words {
                    black_box(map.get(black_box(word.as_bytes()), &pin()));
                }
            });
        }
    })
    .unwrap();
}

fn prepare_btree(words: &[String]) -> BTreeMap<String, u32> {
    let mut map = BTreeMap::new();
    for word in words {
        map.insert(word.clone(), 0);
    }
    map
}

fn btree_insert_get(map: &RwLock<BTreeMap<String, u32>>, words: &[String]) {
    thread::scope(|s| {
        for i in 0..INSERT_THREADS {
            s.spawn(move |_| {
                let words = words
                    .iter()
                    .chain(words.iter())
                    .skip(i * words.len() / INSERT_THREADS)
                    .take(words.len());
                for word in words {
                    map.write().unwrap().insert(word.clone(), i as u32);
                }
            });
        }
        for _ in 0..GET_THREADS {
            s.spawn(|_| {
                for word in words {
                    black_box(map.read().unwrap().get(black_box(word)));
                }
            });
        }
    })
    .unwrap();
}

fn prepare_skipmap(words: &[String]) -> SkipMap<String, u32> {
    let map = SkipMap::new();
    for word in words {
        map.insert(word.clone(), 0);
    }
    map
}

fn skipmap_insert_get(map: &SkipMap<String, u32>, words: &[String]) {
    thread::scope(|s| {
        for i in 0..INSERT_THREADS {
            s.spawn(move |_| {
                let words = words
                    .iter()
                    .chain(words.iter())
                    .skip(i * words.len() / INSERT_THREADS)
                    .take(words.len());
                for word in words {
                    map.insert(word.clone(), i as u32);
                }
            });
        }
        for _ in 0..GET_THREADS {
            s.spawn(|_| {
                for word in words {
                    black_box(map.get(black_box(word)));
                }
            });
        }
    })
    .unwrap();
}

fn bench_insert_get(c: &mut Criterion) {
    let mut words: Vec<String> = File::open("words.txt")
        .map(BufReader::new)
        .and_then(|f| f.lines().collect())
        .unwrap();
    let mut rng = StdRng::seed_from_u64(114514);
    words.shuffle(&mut rng);

    let mut group = c.benchmark_group("get");
    group.bench_with_input(
        BenchmarkId::new("ART", "multi-thread"),
        &words,
        |b, words| {
            let map = prepare_art(words);
            b.iter(|| {
                art_insert_get(&map, words);
            })
        },
    );
    group.bench_with_input(
        BenchmarkId::new("BTreeMap", "multi-thread"),
        &words,
        |b, words| {
            let map = RwLock::new(prepare_btree(words));
            b.iter(|| {
                btree_insert_get(&map, words);
            })
        },
    );
    group.bench_with_input(
        BenchmarkId::new("SkipMap", "multi-thread"),
        &words,
        |b, words| {
            let map = prepare_skipmap(words);
            b.iter(|| {
                skipmap_insert_get(&map, words);
            })
        },
    );
    group.finish();
}

criterion_group!(benches, bench_insert_get);
criterion_main!(benches);
