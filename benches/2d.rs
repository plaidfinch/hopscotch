#![feature(const_int_pow)]

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rand::Rng;

use hopscotch::Queue;

fn random_tags(width: usize) -> impl Iterator<Item = usize> {
    let mut rng = rand::thread_rng();
    std::iter::repeat_with(move || rng.gen_range(0, width + 1))
}

fn unit_queue_from_tags(tags: impl IntoIterator<Item = usize>) -> Queue<usize, ()> {
    let tags = tags.into_iter();
    let mut queue = Queue::with_capacity(tags.size_hint().0);
    for tag in tags {
        queue.push(tag, ());
    }
    queue
}

const MAX_POW_2: u32 = 16;
const LENGTH: usize = 2_usize.pow(MAX_POW_2);

fn bench_create(c: &mut Criterion) {
    let mut group = c.benchmark_group("create");
    for width in (1..=MAX_POW_2).map(|s| 2_usize.pow(s)) {
        let id = BenchmarkId::from_parameter(width);
        group.sample_size(20);
        group.throughput(Throughput::Elements(LENGTH as u64));
        group.bench_with_input(id, &width, |b, width| {
            let tags: Vec<usize> = random_tags(black_box(*width))
                .take(black_box(LENGTH))
                .collect();
            b.iter(|| {
                unit_queue_from_tags(tags.iter().copied());
            });
        });
    }
    group.finish();
}

fn bench_get(c: &mut Criterion) {
    let mut group = c.benchmark_group("get");
    for width in (1..=MAX_POW_2).map(|s| 2_usize.pow(s)) {
        let id = BenchmarkId::from_parameter(width);
        let tags = random_tags(black_box(width)).take(black_box(LENGTH));
        let queue = unit_queue_from_tags(tags);
        group.bench_function(id, |b| {
            let mut rng = rand::thread_rng();
            let i = rng.gen_range(0, LENGTH as u64);
            b.iter(|| queue.get(black_box(i)));
        });
    }
    group.finish();
}

fn bench_after(c: &mut Criterion) {
    let mut group = c.benchmark_group("after");
    for width in (1..=MAX_POW_2).map(|s| 2_usize.pow(s)) {
        for needle_width in (1..MAX_POW_2)
            .map(|s| 2_usize.pow(s))
            .filter(|s| *s <= width)
        {
            let name = format!("width: {}, tags: {}", width, needle_width);
            let id = BenchmarkId::from_parameter(name);
            let tags = random_tags(black_box(width)).take(LENGTH);
            let queue = unit_queue_from_tags(tags);
            group.throughput(Throughput::Elements(needle_width as u64));
            group.bench_function(id, |b| {
                let mut rng = rand::thread_rng();
                let i = rng.gen_range(0, LENGTH as u64);
                let mut needle = Vec::with_capacity(needle_width);
                for _ in 0..needle_width {
                    needle.push(rng.gen_range(0, width + 1));
                }
                b.iter(|| queue.after(black_box(i), &needle));
            });
        }
    }
    group.finish();
}

fn bench_queue(c: &mut Criterion) {
    let mut group = c.benchmark_group("constant size queue");
    for width in (1..=MAX_POW_2).map(|s| 2_usize.pow(s)) {
        let id = BenchmarkId::from_parameter(width);
        group.throughput(Throughput::Elements(1));
        let samples = 100;
        group.sample_size(samples);
        group.bench_with_input(id, &width, |b, width| {
            let tags = random_tags(*width).take(LENGTH);
            let mut queue: Queue<usize, ()> = unit_queue_from_tags(tags);
            b.iter(|| {
                let popped = queue.pop().unwrap();
                queue.push(popped.tag, black_box(()))
            });
        });
    }
}

criterion_group!(
    benches,
    bench_create,
    bench_queue,
    bench_get,
    bench_after,
);
criterion_main!(benches);
