use std::{ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign}, usize};

const MASK: usize = (1 << 6) - 1;

// presumably, below this you'd just use u128 and the other primitives
pub type BitSet192 = BitSet<3>;
pub type BitSet256 = BitSet<4>;
pub type BitSet320 = BitSet<5>;
pub type BitSet384 = BitSet<6>;
pub type BitSet448 = BitSet<7>;
pub type BitSet512 = BitSet<8>;
pub type BitSet576 = BitSet<9>;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BitSet<const N: usize> {
    bits: [u64; N],
}

impl<const N: usize> BitSet<N> {
    pub const ZERO: Self = Self::zero();
    pub const MAX: Self = Self::max();

    pub const fn zero() -> Self {
        Self { bits: [0; N] }
    }

    pub const fn max() -> Self {
        Self { bits: [u64::MAX; N] }
    }

    pub fn insert(&mut self, idx: usize) {
        let bucket = idx >> 6;
        let shift = idx & MASK;
        self.bits[bucket] |= 1 << shift
    }

    pub fn remove(&mut self, idx: usize) {
        let bucket = idx >> 6;
        let shift = idx & MASK;
        self.bits[bucket] &= !(1 << shift);
    }

    pub fn contains(&self, idx: usize) -> bool {
        let bucket = idx >> 6;
        let shift = idx & MASK;
        (self.bits[bucket] & 1 << shift) != 0
    }

    pub fn count(&self) -> u32 {
        self.bits.iter().map(|bucket| if *bucket > 0 { bucket.count_ones() } else { 0 }).sum()
    }

    pub fn next_beyond(&self, idx: usize) -> Option<usize> {
        let mut bucket = idx >> 6;
        let shift = (idx & MASK) + 1;

        if bucket < N && shift < 64 {
            let v = (self.bits[bucket] >> shift).trailing_zeros();
            if v != 64 {
                return Some(bucket * 64 + shift + v as usize);
            }
        }
        bucket += 1;

        while bucket < N {
            if self.bits[bucket] > 0 {
                return Some(bucket * 64 + self.bits[bucket].trailing_zeros() as usize);
            }
            bucket += 1;
        }

        None
    }

    pub fn iter(&self) -> BitSetIter<N> {
        BitSetIter { set: *self, index: usize::MAX }
    }
}

impl<const N: usize> Default for BitSet<N> {
    fn default() -> Self {
        Self::zero()
    }
}

impl<const N: usize> BitAnd for BitSet<N> {
    type Output = BitSet<N>;

    fn bitand(self, rhs: BitSet<N>) -> Self::Output {
        let mut out = self;

        for i in 0..N {
            out.bits[i] &= rhs.bits[i];
        }

        out
    }
}

impl<const N: usize> BitAnd<&BitSet<N>> for BitSet<N> {
    type Output = BitSet<N>;

    fn bitand(self, rhs: &BitSet<N>) -> Self::Output {
        let mut out = self;

        for i in 0..N {
            out.bits[i] &= rhs.bits[i];
        }

        out
    }
}

impl<const N: usize> BitAnd<&BitSet<N>> for &BitSet<N> {
    type Output = BitSet<N>;

    fn bitand(self, rhs: &BitSet<N>) -> Self::Output {
        let mut out = *self;

        for i in 0..N {
            out.bits[i] &= rhs.bits[i];
        }

        out
    }
}

impl<const N: usize> BitAnd<BitSet<N>> for &BitSet<N> {
    type Output = BitSet<N>;

    fn bitand(self, rhs: BitSet<N>) -> Self::Output {
        let mut out = *self;

        for i in 0..N {
            out.bits[i] &= rhs.bits[i];
        }

        out
    }
}

impl<const N: usize> BitAndAssign<BitSet<N>> for BitSet<N> {
    fn bitand_assign(&mut self, rhs: BitSet<N>) {
        for i in 0..N {
            self.bits[i] &= rhs.bits[i];
        }
    }
}

impl<const N: usize> BitAndAssign<&BitSet<N>> for BitSet<N> {
    fn bitand_assign(&mut self, rhs: &BitSet<N>) {
        for i in 0..N {
            self.bits[i] &= rhs.bits[i];
        }
    }
}

impl<const N: usize> BitOr<BitSet<N>> for BitSet<N> {
    type Output = BitSet<N>;

    fn bitor(self, rhs: BitSet<N>) -> Self::Output {
        let mut out = self;

        for i in 0..N {
            out.bits[i] |= rhs.bits[i];
        }

        out
    }
}

impl<const N: usize> BitOr<&BitSet<N>> for BitSet<N> {
    type Output = BitSet<N>;

    fn bitor(self, rhs: &BitSet<N>) -> Self::Output {
        let mut out = self;

        for i in 0..N {
            out.bits[i] |= rhs.bits[i];
        }

        out
    }
}

impl<const N: usize> BitOr<&BitSet<N>> for &BitSet<N> {
    type Output = BitSet<N>;

    fn bitor(self, rhs: &BitSet<N>) -> Self::Output {
        let mut out = *self;

        for i in 0..N {
            out.bits[i] |= rhs.bits[i];
        }

        out
    }
}

impl<const N: usize> BitOr<BitSet<N>> for &BitSet<N> {
    type Output = BitSet<N>;

    fn bitor(self, rhs: BitSet<N>) -> Self::Output {
        let mut out = *self;

        for i in 0..N {
            out.bits[i] |= rhs.bits[i];
        }

        out
    }
}

impl<const N: usize> BitOrAssign<BitSet<N>> for BitSet<N> {
    fn bitor_assign(&mut self, rhs: BitSet<N>) {
        for i in 0..N {
            self.bits[i] |= rhs.bits[i];
        }
    }
}

impl<const N: usize> BitOrAssign<&BitSet<N>> for BitSet<N> {
    fn bitor_assign(&mut self, rhs: &BitSet<N>) {
        for i in 0..N {
            self.bits[i] |= rhs.bits[i];
        }
    }
}

impl<const N: usize> BitXor<BitSet<N>> for BitSet<N> {
    type Output = BitSet<N>;

    fn bitxor(self, rhs: BitSet<N>) -> Self::Output {
        let mut out = self;

        for i in 0..N {
            out.bits[i] ^= rhs.bits[i];
        }

        out
    }
}

impl<const N: usize> BitXor<&BitSet<N>> for BitSet<N> {
    type Output = BitSet<N>;

    fn bitxor(self, rhs: &BitSet<N>) -> Self::Output {
        let mut out = self;

        for i in 0..N {
            out.bits[i] ^= rhs.bits[i];
        }

        out
    }
}

impl<const N: usize> BitXor<&BitSet<N>> for &BitSet<N> {
    type Output = BitSet<N>;

    fn bitxor(self, rhs: &BitSet<N>) -> Self::Output {
        let mut out = *self;

        for i in 0..N {
            out.bits[i] ^= rhs.bits[i];
        }

        out
    }
}

impl<const N: usize> BitXor<BitSet<N>> for &BitSet<N> {
    type Output = BitSet<N>;

    fn bitxor(self, rhs: BitSet<N>) -> Self::Output {
        let mut out = *self;

        for i in 0..N {
            out.bits[i] ^= rhs.bits[i];
        }

        out
    }
}

impl<const N: usize> BitXorAssign<BitSet<N>> for BitSet<N> {
    fn bitxor_assign(&mut self, rhs: BitSet<N>) {
        for i in 0..N {
            self.bits[i] ^= rhs.bits[i];
        }
    }
}

impl<const N: usize> BitXorAssign<&BitSet<N>> for BitSet<N> {
    fn bitxor_assign(&mut self, rhs: &BitSet<N>) {
        for i in 0..N {
            self.bits[i] ^= rhs.bits[i];
        }
    }
}

pub struct BitSetIter<const N: usize> {
    set: BitSet<N>,
    index: usize,
}

impl<const N: usize> Iterator for BitSetIter<N> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index == usize::MAX {
            self.index = 0;
            if self.set.contains(0) {
                return Some(0);
            }
        }

        if self.index == N * 64 {
            return None;
        }

        if let Some(v) = self.set.next_beyond(self.index) {
            self.index = v;
            Some(v)
        } else {
            self.index = N * 64;
            None
        }
    }
}

impl<const N: usize> IntoIterator for BitSet<N> {
    type Item = usize;
    type IntoIter = BitSetIter<N>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bitset_iter() {
        let mut set = BitSet192::default();

        set.insert(20);
        set.insert(46);
        set.insert(100);
        set.insert(191);

        let mut iter = set.iter();

        assert_eq!(20, iter.next().unwrap());
        assert_eq!(46, iter.next().unwrap());
        assert_eq!(100, iter.next().unwrap());
        assert_eq!(191, iter.next().unwrap());
        assert_eq!(None, iter.next());

        assert_eq!(vec![20, 46, 100, 191], set.into_iter().collect::<Vec<_>>());
    }
}
