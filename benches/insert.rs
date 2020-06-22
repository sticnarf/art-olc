#[cfg(not(target_env = "msvc"))]
use jemallocator::Jemalloc;

#[cfg(not(target_env = "msvc"))]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

use art_olc::Tree;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use crossbeam_epoch::pin;
use crossbeam_skiplist::SkipSet;
use crossbeam_utils::thread;
use rand::prelude::*;
use std::{
    collections::{BTreeSet, HashSet},
    fs::File,
    io::{BufRead, BufReader},
    mem,
    sync::Mutex,
    time::{Duration, Instant},
};

const THREAD_NUM: usize = 8;

fn insert_art(words: Vec<String>) -> Tree<()> {
    let set = Tree::new();
    for word in words {
        let guard = pin();
        set.insert(word.as_bytes(), (), &guard);
    }
    set
}

fn insert_art_multithread(mut words: Vec<String>) -> Tree<()> {
    let set = Tree::new();
    let chunk_size = words.len() / THREAD_NUM + 1;
    thread::scope(|s| {
        for chunk in words.chunks_mut(chunk_size) {
            s.spawn(|_| {
                for word in chunk {
                    let guard = pin();
                    set.insert(word.as_bytes(), (), &guard);
                }
            });
        }
    })
    .unwrap();
    set
}

fn insert_btree(words: Vec<String>) -> BTreeSet<String> {
    let mut set = BTreeSet::new();
    for word in words {
        set.insert(word);
    }
    set
}

fn insert_btree_multithread(mut words: Vec<String>) -> Mutex<BTreeSet<String>> {
    let set = Mutex::new(BTreeSet::new());
    let chunk_size = words.len() / THREAD_NUM + 1;
    thread::scope(|s| {
        for chunk in words.chunks_mut(chunk_size) {
            s.spawn(|_| {
                for word in chunk {
                    set.lock()
                        .unwrap()
                        .insert(mem::replace(word, String::new()));
                }
            });
        }
    })
    .unwrap();
    set
}

fn insert_hashset(words: Vec<String>) -> HashSet<String> {
    let mut set = HashSet::new();
    for word in words {
        set.insert(word);
    }
    set
}

fn insert_skiplist(words: Vec<String>) -> SkipSet<String> {
    let list = SkipSet::new();
    for word in words {
        list.insert(word);
    }
    list
}

fn insert_skiplist_multithread(mut words: Vec<String>) -> SkipSet<String> {
    let set = SkipSet::new();
    let chunk_size = words.len() / THREAD_NUM + 1;
    thread::scope(|s| {
        for chunk in words.chunks_mut(chunk_size) {
            s.spawn(|_| {
                for word in chunk {
                    set.insert(mem::replace(word, String::new()));
                }
            });
        }
    })
    .unwrap();
    set
}

fn bench_insert(c: &mut Criterion) {
    let mut words: Vec<String> = File::open("words.txt")
        .map(BufReader::new)
        .and_then(|f| f.lines().collect())
        .unwrap();
    let mut rng = StdRng::seed_from_u64(114514);
    words.shuffle(&mut rng);

    let mut group = c.benchmark_group("insert");
    group.bench_with_input(
        BenchmarkId::new("ART", "single-thread"),
        &words,
        |b, words| {
            b.iter_custom(|iter| {
                let mut elapsed = Duration::default();
                for _ in 0..iter {
                    let words = words.clone();
                    let start = Instant::now();
                    let tree = insert_art(words);
                    elapsed += start.elapsed();
                    drop(tree);
                }
                elapsed
            })
        },
    );
    group.bench_with_input(
        BenchmarkId::new("ART", "multi-thread"),
        &words,
        |b, words| {
            b.iter_custom(|iter| {
                let mut elapsed = Duration::default();
                for _ in 0..iter {
                    let words = words.clone();
                    let start = Instant::now();
                    let tree = insert_art_multithread(words);
                    elapsed += start.elapsed();
                    drop(tree);
                }
                elapsed
            })
        },
    );
    group.bench_with_input(
        BenchmarkId::new("BTreeSet", "single-thread"),
        &words,
        |b, words| {
            b.iter_custom(|iter| {
                let mut elapsed = Duration::default();
                for _ in 0..iter {
                    let words = words.clone();
                    let start = Instant::now();
                    let tree = insert_btree(words);
                    elapsed += start.elapsed();
                    drop(tree);
                }
                elapsed
            })
        },
    );
    group.bench_with_input(
        BenchmarkId::new("BTreeSet", "multi-thread"),
        &words,
        |b, words| {
            b.iter_custom(|iter| {
                let mut elapsed = Duration::default();
                for _ in 0..iter {
                    let words = words.clone();
                    let start = Instant::now();
                    let tree = insert_btree_multithread(words);
                    elapsed += start.elapsed();
                    drop(tree);
                }
                elapsed
            })
        },
    );
    group.bench_with_input(
        BenchmarkId::new("HashSet", "single-thread"),
        &words,
        |b, words| {
            b.iter_custom(|iter| {
                let mut elapsed = Duration::default();
                for _ in 0..iter {
                    let words = words.clone();
                    let words = words.clone();
                    let start = Instant::now();
                    let tree = insert_hashset(words);
                    elapsed += start.elapsed();
                    drop(tree);
                }
                elapsed
            })
        },
    );
    group.bench_with_input(
        BenchmarkId::new("SkipSet", "single-thread"),
        &words,
        |b, words| {
            b.iter_custom(|iter| {
                let mut elapsed = Duration::default();
                for _ in 0..iter {
                    let words = words.clone();
                    let start = Instant::now();
                    let tree = insert_skiplist(words);
                    elapsed += start.elapsed();
                    drop(tree);
                }
                elapsed
            })
        },
    );
    group.bench_with_input(
        BenchmarkId::new("SkipSet", "multi-thread"),
        &words,
        |b, words| {
            b.iter_custom(|iter| {
                let mut elapsed = Duration::default();
                for _ in 0..iter {
                    let words = words.clone();
                    let start = Instant::now();
                    let tree = insert_skiplist_multithread(words);
                    elapsed += start.elapsed();
                    drop(tree);
                }
                elapsed
            })
        },
    );
    group.finish();
}

criterion_group!(benches, bench_insert);
criterion_main!(benches);
