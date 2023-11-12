use std::str::FromStr;

use aoc_std::{collections::CharSet, types::Alpha};
use divan::{black_box, Bencher};
use rustc_hash::FxHashSet;

fn main() {
    divan::main()
}

const LOWER: &str = "abcdefghijklmnopqrstuvwxyz";
const UPPER: &str = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
const COMPLETE: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
const PARTIAL: &str = "acegikmoqsuwyACEGIKMOQSUWY";
const DEGENERATE: &str = "abcdDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDEFGHIJ";

trait ComparableSet: Default {
    type ArgType;

    fn from_input(input: &str) -> Self;
    fn arg_from_char(ch: char) -> Self::ArgType;
    fn check_contains(&self, ch: &Self::ArgType) -> bool;
    fn check_insert(&mut self, ch: Self::ArgType);
    fn check_remove(&mut self, ch: &Self::ArgType);
    fn check_is_subset(&self, other: &Self) -> bool;
    fn check_is_superset(&self, other: &Self) -> bool;
    fn check_is_disjoint(&self, other: &Self) -> bool;
    fn check_union(&self, other: &Self) -> Self;
    fn check_intersection(&self, other: &Self) -> Self;

    fn input_to_args(input: &str) -> Vec<Self::ArgType> {
        input
            .chars()
            .map(|ch| <Self as ComparableSet>::arg_from_char(ch))
            .collect()
    }
}

impl ComparableSet for FxHashSet<char> {
    type ArgType = char;

    fn from_input(input: &str) -> Self {
        FxHashSet::from_iter(input.chars())
    }

    fn arg_from_char(ch: char) -> Self::ArgType {
        ch
    }

    fn check_contains(&self, ch: &Self::ArgType) -> bool {
        self.contains(ch)
    }

    fn check_insert(&mut self, ch: Self::ArgType) {
        self.insert(ch);
    }

    fn check_remove(&mut self, ch: &Self::ArgType) {
        self.remove(ch);
    }

    fn check_is_subset(&self, other: &Self) -> bool {
        self.is_subset(other)
    }

    fn check_is_superset(&self, other: &Self) -> bool {
        self.is_superset(other)
    }

    fn check_is_disjoint(&self, other: &Self) -> bool {
        self.is_disjoint(other)
    }

    fn check_union(&self, other: &Self) -> Self {
        self | other
    }

    fn check_intersection(&self, other: &Self) -> Self {
        self & other
    }
}

impl ComparableSet for CharSet {
    type ArgType = Alpha;

    fn from_input(input: &str) -> Self {
        CharSet::from_str(input).unwrap()
    }

    fn arg_from_char(ch: char) -> Self::ArgType {
        Alpha::try_from(ch).unwrap()
    }

    fn check_contains(&self, ch: &Self::ArgType) -> bool {
        self.contains(ch)
    }

    fn check_insert(&mut self, ch: Self::ArgType) {
        self.insert(ch);
    }

    fn check_remove(&mut self, ch: &Self::ArgType) {
        self.remove(ch);
    }

    fn check_is_subset(&self, other: &Self) -> bool {
        self.is_subset(other)
    }

    fn check_is_superset(&self, other: &Self) -> bool {
        self.is_superset(other)
    }

    fn check_is_disjoint(&self, other: &Self) -> bool {
        self.is_disjoint(other)
    }

    fn check_union(&self, other: &Self) -> Self {
        *self | *other
    }

    fn check_intersection(&self, other: &Self) -> Self {
        *self & *other
    }
}

mod construction {
    use super::*;

    #[divan::bench(
        types = [
            FxHashSet<char>,
            CharSet,
        ]
    )]
    fn complete<T: ComparableSet>(bencher: Bencher) {
        bencher.bench(|| T::from_input(black_box(COMPLETE)))
    }

    #[divan::bench(
        types = [
            FxHashSet<char>,
            CharSet,
        ]
    )]
    fn degenerate<T: ComparableSet>(bencher: Bencher) {
        bencher.bench(|| T::from_input(black_box(DEGENERATE)))
    }
}

#[divan::bench(
    types = [
        FxHashSet<char>,
        CharSet,
    ]
)]
fn contains<T: ComparableSet>(bencher: Bencher) {
    bencher
        .with_inputs(|| {
            (
                T::from_input(PARTIAL),
                T::arg_from_char('a'),
                T::arg_from_char('B'),
            )
        })
        .bench_refs(|(set, exist, not_exist)| {
            black_box(set.check_contains(exist));
            black_box(set.check_contains(not_exist));
        })
}

const LENS: &[usize] = &[1, 10, 20, 52];

#[divan::bench(
    types = [
        FxHashSet<char>,
        CharSet,
    ],
    consts = LENS
)]
fn insert<T: ComparableSet, const N: usize>(bencher: Bencher) {
    bencher
        .counter(N)
        .with_inputs(|| (T::default(), T::input_to_args(COMPLETE).into_iter().take(N)))
        .bench_values(|(mut set, input)| {
            for ch in input {
                black_box(set.check_insert(ch));
            }
        })
}

#[divan::bench(
    types = [
        FxHashSet<char>,
        CharSet,
    ],
    consts = LENS
)]
fn remove<T: ComparableSet, const N: usize>(bencher: Bencher) {
    bencher
        .counter(N)
        .with_inputs(|| {
            (
                T::from_input(COMPLETE),
                T::input_to_args(COMPLETE).into_iter().take(N),
            )
        })
        .bench_refs(|(set, input)| {
            for ch in input {
                black_box(set.check_remove(&ch));
            }
        })
}

#[divan::bench(
    types = [
        FxHashSet<char>,
        CharSet,
    ]
)]
fn is_subset<T: ComparableSet>(bencher: Bencher) {
    bencher
        .with_inputs(|| (T::from_input(COMPLETE), T::from_input(PARTIAL)))
        .bench_refs(|(s1, s2)| black_box(s2.check_is_subset(s1)))
}

#[divan::bench(
    types = [
        FxHashSet<char>,
        CharSet,
    ]
)]
fn is_superset<T: ComparableSet>(bencher: Bencher) {
    bencher
        .with_inputs(|| (T::from_input(COMPLETE), T::from_input(PARTIAL)))
        .bench_refs(|(s1, s2)| black_box(s1.check_is_superset(s2)))
}

#[divan::bench(
    types = [
        FxHashSet<char>,
        CharSet,
    ]
)]
fn is_disjoint<T: ComparableSet>(bencher: Bencher) {
    bencher
        .with_inputs(|| (T::from_input(UPPER), T::from_input(LOWER)))
        .bench_refs(|(s1, s2)| black_box(s1.check_is_disjoint(s2)))
}

#[divan::bench(
    types = [
        FxHashSet<char>,
        CharSet,
    ]
)]
fn new_set_from_union<T: ComparableSet>(bencher: Bencher) {
    bencher
        .with_inputs(|| (T::from_input(UPPER), T::from_input(PARTIAL)))
        .bench_refs(|(s1, s2)| black_box(s1.check_union(s2)))
}

#[divan::bench(
    types = [
        FxHashSet<char>,
        CharSet,
    ]
)]
fn new_set_from_intersection<T: ComparableSet>(bencher: Bencher) {
    bencher
        .with_inputs(|| (T::from_input(UPPER), T::from_input(PARTIAL)))
        .bench_refs(|(s1, s2)| black_box(s1.check_intersection(s2)))
}
