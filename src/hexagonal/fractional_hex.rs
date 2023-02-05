use std::{
    fmt::Display,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use super::Hex;

/// A floating point coordinate in hexagonal space.
///
/// A way to look at hexagonal grids is to see that there are three primary axes, unlike the two we have for rectangular grids.
/// The constraint for [cube] coordinates is that `q + r + s == 0`.
///
/// Because of this constraint we can mitigate `s` because it will always equal `-q - r`.
/// We call this [axial] coordinates.
///
/// ```txt
///         +---+
///        /     \
///   +---+ 0, -1 +---+
///  /     \     /     \
/// + -1, 0 +---+ 1, -1 +
///  \     /     \     /
///   +---+  0,0  +---+
///  /     \     /     \
/// + -1, 1 +---+  1,0  +
///  \     /     \     /
///   +---+  0,1  +---+
///        \     /
///         +---+
/// ```
///
/// [cube]: https://www.redblobgames.com/grids/hexagons/#coordinates-cube
/// [axial]: https://www.redblobgames.com/grids/hexagons/#coordinates-axial
#[derive(Default, Debug, Clone, Copy, PartialEq)]
pub struct FHex {
    q: f32,
    r: f32,
}

impl FHex {
    /// Alias to `Self::new(0., 0.)`
    pub const ZERO: Self = Self::new(0., 0.);

    /// Alias to `Self::new(0., 0.)`
    pub const ONE: Self = Self::new(1., 1.);

    /// Hexagon towards `q`, `-r`
    pub const QR: Self = Self::new(1., -1.);
    /// Hexagon towards `q`, `-s`
    pub const QS: Self = Self::new(1., 0.);
    /// Hexagon towards `r`, `-q`
    pub const RQ: Self = Self::new(-1., 1.);
    /// Hexagon towards `r`, `-s`
    pub const RS: Self = Self::new(0., 1.);
    /// Hexagon towards `s`, `-q`
    pub const SQ: Self = Self::new(-1., 0.);
    /// Hexagon towards `s`, `-r`
    pub const SR: Self = Self::new(0., -1.);

    /// Hexagon diagonal towards `q`
    pub const QQ: Self = Self::new(2., -1.);
    /// Hexagon diagonal towards `r`
    pub const RR: Self = Self::new(-1., 2.);
    /// Hexagon diagonal towards `s`
    pub const SS: Self = Self::new(-1., -1.);

    /// Create a hexagon from axial coordinates, alias to `new_axial`
    #[inline]
    #[must_use]
    pub const fn new(q: f32, r: f32) -> Self {
        Self { q, r }
    }

    /// Gets position on the `q` axis
    #[inline]
    #[must_use]
    pub fn q(self) -> f32 {
        self.q
    }

    /// Gets position on the `r` axis
    #[inline]
    #[must_use]
    pub fn r(self) -> f32 {
        self.r
    }

    /// Computes position on the `s` axis
    #[inline]
    #[must_use]
    pub fn s(self) -> f32 {
        -self.q - self.r
    }

    /// Rounds this floating point hex to the nearest [`Hex`]
    pub fn round(self) -> Hex {
        let mut q_rounded = self.q.round();
        let mut r_rounded = self.r.round();

        let q_rem = self.q - q_rounded;
        let r_rem = self.r - r_rounded;

        if q_rem.abs() >= r_rem.abs() {
            q_rounded += r_rem.mul_add(0.5, q_rem).round();
        } else {
            r_rounded += q_rem.mul_add(0.5, r_rem).round();
        }

        Hex::new(q_rounded as i32, r_rounded as i32)
    }

    /// Computes coordinates signed distance from center
    #[inline]
    #[must_use]
    pub fn length(self) -> f32 {
        (self.q.abs() + self.r.abs() + self.s().abs()) / 2.
    }

    /// Computes coordinates signed distance from another hex
    ///
    /// See [`Self::udistance`] for the unsigned version
    #[inline]
    #[must_use]
    pub fn distance(self, other: Self) -> f32 {
        (self - other).length()
    }

    /// Rotate hex counter clockwise
    #[inline]
    #[must_use]
    pub fn rotate_left(self) -> Self {
        Self {
            q: -self.s(),
            r: -self.q,
        }
    }

    /// Rotate hex counter clockwise around `center`
    #[inline]
    #[must_use]
    pub fn rotate_left_around(self, center: Self) -> Self {
        (self - center).rotate_left() + center
    }

    /// Rotate hex clockwise
    #[inline]
    #[must_use]
    pub fn rotate_right(self) -> Self {
        Self {
            q: -self.r,
            r: -self.s(),
        }
    }

    /// Rotate hex clockwise around `center`
    #[inline]
    #[must_use]
    pub fn rotate_right_around(self, center: Self) -> Self {
        (self - center).rotate_right() + center
    }

    /// Reflect hex over `center`
    ///
    /// The same as [`Self::const_neg`] but not over [`Hex::ZERO`]
    #[inline]
    #[must_use]
    pub fn reflect_over(self, center: Self) -> Self {
        -(self - center) + center
    }

    /// Reflect hex across the `q` axis over [`Hex::ZERO`]
    #[inline]
    #[must_use]
    pub fn reflect_q(self) -> Self {
        Self {
            q: self.q,
            r: self.s(),
        }
    }

    /// Reflect hex across the `q` axis over `center`
    #[inline]
    #[must_use]
    pub fn reflect_q_over(self, center: Self) -> Self {
        (self - center).reflect_q() + center
    }

    /// Reflect hex across the `r` axis over [`Hex::ZERO`]
    #[inline]
    #[must_use]
    pub fn reflect_r(self) -> Self {
        Self {
            q: self.s(),
            r: self.r,
        }
    }

    /// Reflect hex across the `r` axis over `center`
    #[inline]
    #[must_use]
    pub fn reflect_r_over(self, center: Self) -> Self {
        (self - center).reflect_r() + center
    }

    /// Reflect hex across the `s` axis over [`Hex::ZERO`]
    #[inline]
    #[must_use]
    pub fn reflect_s(self) -> Self {
        Self {
            q: self.r,
            r: self.q,
        }
    }

    /// Reflect hex across the `s` axis over `center`
    #[inline]
    #[must_use]
    pub fn reflect_s_over(self, center: Self) -> Self {
        (self - center).reflect_s() + center
    }
}

impl Add<Self> for FHex {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            q: self.q.add(rhs.q),
            r: self.r.add(rhs.r),
        }
    }
}

impl AddAssign<Self> for FHex {
    fn add_assign(&mut self, rhs: Self) {
        self.q.add_assign(rhs.q);
        self.r.add_assign(rhs.r);
    }
}

impl Sub<Self> for FHex {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            q: self.q.sub(rhs.q),
            r: self.r.sub(rhs.r),
        }
    }
}

impl SubAssign<Self> for FHex {
    fn sub_assign(&mut self, rhs: Self) {
        self.q.sub_assign(rhs.q);
        self.r.sub_assign(rhs.r);
    }
}

impl Mul<f32> for FHex {
    type Output = Self;

    fn mul(self, rhs: f32) -> Self::Output {
        Self {
            q: self.q.mul(rhs),
            r: self.r.mul(rhs),
        }
    }
}

impl Mul<FHex> for f32 {
    type Output = FHex;

    fn mul(self, rhs: FHex) -> Self::Output {
        FHex {
            q: self.mul(rhs.q),
            r: self.mul(rhs.r),
        }
    }
}

impl MulAssign<f32> for FHex {
    fn mul_assign(&mut self, rhs: f32) {
        self.q.mul_assign(rhs);
        self.r.mul_assign(rhs);
    }
}

impl Neg for FHex {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            q: self.q.neg(),
            r: self.r.neg(),
        }
    }
}

impl From<Hex> for FHex {
    fn from(value: Hex) -> Self {
        Self {
            q: value.q() as f32,
            r: value.r() as f32,
        }
    }
}

impl From<(f32, f32)> for FHex {
    fn from((q, r): (f32, f32)) -> Self {
        Self { q, r }
    }
}

impl From<[f32; 2]> for FHex {
    fn from([q, r]: [f32; 2]) -> Self {
        Self { q, r }
    }
}

impl Display for FHex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}, {}]", self.q, self.r)
    }
}

#[cfg(test)]
mod tests {
    use super::{FHex, Hex};

    #[test]
    fn addition() {
        assert_eq!(FHex::ZERO + FHex::ZERO, FHex::ZERO);
        assert_eq!(FHex::ZERO + FHex::ONE, FHex::ONE);
        assert_eq!(FHex::ONE + FHex::ONE, FHex::new(2., 2.));
        assert_eq!(FHex::ONE + FHex::new(3., 4.), FHex::new(4., 5.));
    }

    #[test]
    fn subtraction() {
        assert_eq!(FHex::ZERO - FHex::ZERO, FHex::ZERO);
        assert_eq!(FHex::ONE - FHex::ZERO, FHex::ONE);
        assert_eq!(FHex::ONE - FHex::ONE, FHex::ZERO);
        assert_eq!(FHex::ONE - FHex::new(2., 2.), FHex::new(-1., -1.));
        assert_eq!(FHex::ONE - FHex::new(4., 5.), FHex::new(-3., -4.));
    }

    #[test]
    fn multiplication() {
        assert_eq!(FHex::ONE * 0., FHex::ZERO);
        assert_eq!(FHex::ONE * 1., FHex::ONE);
        assert_eq!(FHex::new(2., 2.) * 1., FHex::new(2., 2.));
        assert_eq!(1. * FHex::new(5., 6.), FHex::new(5., 6.));
        assert_eq!(FHex::new(2., 3.) * 2., FHex::new(4., 6.));
    }

    #[test]
    fn negation() {
        assert_eq!(-FHex::ZERO, FHex::ZERO);
        assert_eq!(-FHex::ONE, FHex::new(-1., -1.));
        assert_eq!(-(-FHex::ONE), FHex::ONE);
    }

    #[test]
    fn length() {
        assert_eq!(FHex::ZERO.length(), 0.);
        assert_eq!(FHex::ONE.length(), 2.);
    }

    #[test]
    fn distance() {
        assert_eq!(FHex::ZERO.distance(FHex::ZERO), 0.);
        assert_eq!(FHex::ONE.distance(FHex::ONE), 0.);
        assert_eq!(FHex::ONE.distance(FHex::ZERO), 2.);
    }

    #[test]
    fn reflection() {
        assert_eq!(FHex::ONE.reflect_over(FHex::ZERO), FHex::new(-1., -1.));
        assert_eq!(FHex::new(2., 1.).reflect_over(FHex::ONE), FHex::new(0., 1.));

        assert_eq!(FHex::new(2., 1.).reflect_q(), FHex::new(2., -3.));
        assert_eq!(
            FHex::new(2., 1.).reflect_q_over(FHex::ZERO),
            FHex::new(2., -3.)
        );
        assert_eq!(
            FHex::new(2., 1.).reflect_q_over(FHex::ONE),
            FHex::new(2., 0.)
        );

        assert_eq!(FHex::new(2., 1.).reflect_r(), FHex::new(-3., 1.));
        assert_eq!(
            FHex::new(2., 1.).reflect_r_over(FHex::ZERO),
            FHex::new(-3., 1.)
        );
        assert_eq!(
            FHex::new(2., 1.).reflect_r_over(FHex::ONE),
            FHex::new(0., 1.)
        );

        assert_eq!(FHex::new(2., 1.).reflect_s(), FHex::new(1., 2.));
        assert_eq!(
            FHex::new(2., 1.).reflect_s_over(FHex::ZERO),
            FHex::new(1., 2.)
        );
        assert_eq!(
            FHex::new(2., 1.).reflect_s_over(FHex::ONE),
            FHex::new(1., 2.)
        );
    }

    #[test]
    fn rounding() {
        assert_eq!(FHex::ZERO.round(), Hex::ZERO);
        assert_eq!(FHex::ONE.round(), Hex::ONE);
        assert_eq!(FHex::new(1.1, 1.).round(), Hex::ONE);
        assert_eq!(FHex::new(1.1, 0.4).round(), Hex::new(1, 0));
    }
}
