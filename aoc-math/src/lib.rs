pub trait ModInv {
    fn mod_inv(a: Self, m: Self) -> Self;
}

macro_rules! impl_integers {
    ($($x:ty),+ $(,)?) => {
        $(
            impl ModInv for $x {
                fn mod_inv(a0: Self, m0: Self) -> Self {
                    if m0 == 1 { return 1 }

                    let (mut a, mut m, mut x0, mut inv) = (a0, m0, 0, 1);

                    while a > 1 {
                        inv -= (a / m) * x0;
                        a = a % m;
                        std::mem::swap(&mut a, &mut m);
                        std::mem::swap(&mut x0, &mut inv);
                    }

                    if inv < 0 { inv += m0 }
                    inv
                }
            }
        )*
    };
}

impl_integers!(i8, i16, i32, i64, i128, isize);
