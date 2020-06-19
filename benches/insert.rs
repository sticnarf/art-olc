#[cfg(not(target_env = "msvc"))]
use jemallocator::Jemalloc;

#[cfg(not(target_env = "msvc"))]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

use art_olc::Tree;
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use crossbeam_epoch::pin;
use rand::prelude::*;
use std::{
    collections::BTreeSet,
    fs::File,
    io::{BufRead, BufReader},
    time::{Duration, Instant},
};

fn insert_art(words: &[String]) -> Tree<()> {
    let mut tree = Tree::new();
    for word in words {
        let guard = pin();
        tree.insert(word.as_bytes(), (), &guard);
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

fn fibonacci_fast(n: u64) -> u64 {
    let mut a = 0;
    let mut b = 1;

    match n {
        0 => b,
        _ => {
            for _ in 0..n {
                let c = a + b;
                a = b;
                b = c;
            }
            b
        }
    }
}

fn bench_insert(c: &mut Criterion) {
    let mut words: Vec<String> = File::open("words.txt")
        .map(BufReader::new)
        .and_then(|f| f.lines().collect())
        .unwrap();
    let mut rng = StdRng::seed_from_u64(114514);
    words.shuffle(&mut rng);

    let mut group = c.benchmark_group("insert");
    group.bench_with_input(BenchmarkId::new("ART", "words"), &words, |b, words| {
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
    });
    group.bench_with_input(BenchmarkId::new("BTreeSet", "words"), &words, |b, words| {
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
    });
    group.finish();
}

criterion_group!(benches, bench_insert);
criterion_main!(benches);
