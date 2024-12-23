use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign};

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
    pub fn insert(&mut self, idx: usize) {
        let bucket = idx / 64;
        let shift = idx % 64;
        self.bits[bucket] |= 1 << shift
    }

    pub fn remove(&mut self, idx: usize) {
        let bucket = idx / 64;
        let shift = idx % 64;
        self.bits[bucket] &= !(1 << shift);
    }

    pub fn contains(&self, idx: usize) -> bool {
        let bucket = idx / 64;
        let shift = idx % 64;
        (self.bits[bucket] & 1 << shift) != 0
    }

    pub fn count(&self) -> u32 {
        self.bits.iter().map(|bucket| bucket.count_ones()).sum()
    }

    pub fn zero() -> Self {
        Self { bits: [0; N] }
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
