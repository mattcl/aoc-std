use std::{
    num::ParseIntError,
    ops::{Deref, DerefMut},
    str::FromStr,
};

use aoc_std::collections::IntVec;
use divan::{black_box, Bencher};

fn main() {
    divan::main()
}

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct BaselineVec(Vec<i64>);

impl Deref for BaselineVec {
    type Target = Vec<i64>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for BaselineVec {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl FromStr for BaselineVec {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let v = s
            .trim()
            .split("\n")
            .map(|l| l.parse::<i64>())
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Self(v))
    }
}

const LENS: &[usize] = &[1, 100, 500, 1_000, 10_000];

mod construction {
    use super::*;
    use rand::Rng;

    #[divan::bench(
        types = [
            BaselineVec,
            IntVec,
        ],
        consts = LENS
    )]
    fn from_str<T: FromStr, const N: usize>(bencher: Bencher) {
        bencher
            .counter(N)
            .with_inputs(|| {
                let mut rng = rand::thread_rng();
                let raw = (0..N)
                    .map(|_| rng.gen::<i64>().to_string())
                    .collect::<Vec<_>>();
                raw.join("\n")
            })
            .bench_refs(|input| T::from_str(black_box(input)))
    }
}
