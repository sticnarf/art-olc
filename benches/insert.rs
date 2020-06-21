#[cfg(not(target_env = "msvc"))]
use jemallocator::Jemalloc;

#[cfg(not(target_env = "msvc"))]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

use art_olc::Tree;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use crossbeam_epoch::pin;
use crossbeam_skiplist::SkipSet;
use crossbeam_utils::sync::WaitGroup;
use rand::prelude::*;
use std::{
    collections::BTreeSet,
    fs::File,
    io::{BufRead, BufReader},
    sync::{Arc, Mutex},
    thread,
    time::{Duration, Instant},
};

const THREAD_NUM: usize = 8;

fn insert_art(words: &[String]) -> Tree<()> {
    let tree = Tree::new();
    for word in words {
        let guard = pin();
        tree.insert(word.as_bytes(), (), &guard);
    }
    tree
}

fn insert_art_multithread(words: &[String]) -> Arc<Tree<()>> {
    let tree = Arc::new(Tree::new());
    let wg = WaitGroup::new();
    let chunk_size = words.len() / THREAD_NUM + 1;
    for chunk in words.chunks(chunk_size) {
        let tree = tree.clone();
        let wg = wg.clone();
        let chunk = unsafe { &*(chunk as *const [String]) };
        thread::spawn(move || {
            for word in chunk {
                let guard = pin();
                tree.insert(word.as_bytes(), (), &guard);
            }
            drop(wg);
        });
    }
    tree
}

fn insert_btree(words: &[String]) -> BTreeSet<String> {
    let mut tree = BTreeSet::new();
    for word in words {
        tree.insert(word.to_owned());
    }
    tree
}

fn insert_btree_multithread(words: &[String]) -> Arc<Mutex<BTreeSet<String>>> {
    let tree = Arc::new(Mutex::new(BTreeSet::new()));
    let wg = WaitGroup::new();
    let chunk_size = words.len() / THREAD_NUM + 1;
    for chunk in words.chunks(chunk_size) {
        let tree = tree.clone();
        let wg = wg.clone();
        let chunk = unsafe { &*(chunk as *const [String]) };
        thread::spawn(move || {
            for word in chunk {
                tree.lock().unwrap().insert(word.to_owned());
            }
            drop(wg);
        });
    }
    tree
}

fn insert_skiplist(words: &[String]) -> SkipSet<String> {
    let list = SkipSet::new();
    for word in words {
        list.insert(word.to_owned());
    }
    list
}

fn insert_skiplist_multithread(words: &[String]) -> Arc<SkipSet<String>> {
    let list = Arc::new(SkipSet::new());
    let wg = WaitGroup::new();
    let chunk_size = words.len() / THREAD_NUM + 1;
    for chunk in words.chunks(chunk_size) {
        let list = list.clone();
        let wg = wg.clone();
        let chunk = unsafe { &*(chunk as *const [String]) };
        thread::spawn(move || {
            for word in chunk {
                list.insert(word.to_owned());
            }
            drop(wg);
        });
    }
    list
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
        BenchmarkId::new("SkipSet", "single-thread"),
        &words,
        |b, words| {
            b.iter_custom(|iter| {
                let mut elapsed = Duration::default();
                for _ in 0..iter {
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
