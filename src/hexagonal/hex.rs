use std::{
    fmt::Display,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

use super::FHex;

/// A coordinate in hexagonal space.
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
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Hex {
    q: i32,
    r: i32,
}

impl Hex {
    /// Alias to `Self::new(0, 0)`
    pub const ZERO: Self = Self::new(0, 0);

    /// Alias to `Self::new(0, 0)`
    pub const ONE: Self = Self::new(1, 1);

    /// Hexagon towards `q`, `-r`
    pub const QR: Self = Self::new(1, -1);
    /// Hexagon towards `q`, `-s`
    pub const QS: Self = Self::new(1, 0);
    /// Hexagon towards `r`, `-q`
    pub const RQ: Self = Self::new(-1, 1);
    /// Hexagon towards `r`, `-s`
    pub const RS: Self = Self::new(0, 1);
    /// Hexagon towards `s`, `-q`
    pub const SQ: Self = Self::new(-1, 0);
    /// Hexagon towards `s`, `-r`
    pub const SR: Self = Self::new(0, -1);

    /// Hexagon diagonal towards `q`
    pub const QQ: Self = Self::new(2, -1);
    /// Hexagon diagonal towards `r`
    pub const RR: Self = Self::new(-1, 2);
    /// Hexagon diagonal towards `s`
    pub const SS: Self = Self::new(-1, -1);

    /// Collection of all directions
    ///
    /// ```txt
    ///         +---+
    ///        /     \
    ///   +---+  6th  +---+
    ///  /     \     /     \
    /// +  5th  +---+  1st  +
    ///  \     /     \     /
    ///   +---+  0,0  +---+
    ///  /     \     /     \
    /// +  4th  +---+  2nd  +
    ///  \     /     \     /
    ///   +---+  3rd  +---+
    ///        \     /
    ///         +---+
    /// ```
    ///
    /// Starts at `Hex(1, -1)` goes clockwise to `Hex(-1, 1)`
    pub const DIRECTIONS: [Self; 6] = [Self::QR, Self::QS, Self::RS, Self::RQ, Self::SQ, Self::SR];

    /// Collection of all diagonals
    ///
    /// ```txt
    ///           \     /
    ///       5th  +---+  6th
    ///     \     /     \     /
    ///      +---+       +---+
    ///     /     \     /     \
    /// ---+       +---+       +---
    ///     \     /     \     /
    /// 4th  +---+  0,0  +---+  1st
    ///     /     \     /     \
    /// ---+       +---+       +---
    ///     \     /     \     /
    ///      +---+       +---+
    ///     /     \     /     \
    ///       3rd  +---+  2nd  
    ///           /     \
    /// ```
    ///
    /// Starts at `Hex(2, -1)` goes clockwise to `Hex(1, -2)`
    pub const DIAGONALS: [Self; 6] = [
        Self::QQ,
        Self::SS.const_neg(),
        Self::RR,
        Self::QQ.const_neg(),
        Self::SS,
        Self::RR.const_neg(),
    ];

    /// Create a hexagon from axial coordinates, alias to `new_axial`
    #[inline]
    #[must_use]
    pub const fn new(q: i32, r: i32) -> Self {
        Self { q, r }
    }

    /// Create a hexagon from axial coordinates
    #[inline]
    #[must_use]
    pub const fn new_axial(q: i32, r: i32) -> Self {
        Self { q, r }
    }

    /// Create a hexagon from cube coordinates
    ///
    /// # Panics
    /// Panics if the sum of coordinates is not equal to zero
    #[inline]
    #[must_use]
    pub const fn new_cube(q: i32, r: i32, s: i32) -> Self {
        assert!(q + r + s == 0);
        Self { q, r }
    }

    /// Gets position on the `q` axis
    #[inline]
    #[must_use]
    pub const fn q(self) -> i32 {
        self.q
    }

    /// Gets position on the `r` axis
    #[inline]
    #[must_use]
    pub const fn r(self) -> i32 {
        self.r
    }

    /// Computes position on the `s` axis
    #[inline]
    #[must_use]
    pub const fn s(self) -> i32 {
        -self.q - self.r
    }

    /// const version of [`Add`]
    pub const fn const_add(self, rhs: Self) -> Self {
        Self {
            q: self.q + rhs.q,
            r: self.r + rhs.r,
        }
    }

    /// const version of [`Sub`]
    pub const fn const_sub(self, rhs: Self) -> Self {
        Self {
            q: self.q - rhs.q,
            r: self.r - rhs.r,
        }
    }

    /// const version of [`Mul`]
    pub const fn const_mul(self, rhs: i32) -> Self {
        Self {
            q: self.q * rhs,
            r: self.r * rhs,
        }
    }

    /// const version of [`Neg`]
    ///
    /// The same as [`Self::reflect_over`] but over [`Hex::ZERO`]
    pub const fn const_neg(self) -> Self {
        Self {
            q: -self.q,
            r: -self.r,
        }
    }

    /// Computes coordinates signed distance from center
    ///
    /// See [`Self::ulength`] for the unsigned version
    #[inline]
    #[must_use]
    pub const fn length(self) -> i32 {
        (self.q.abs() + self.r.abs() + self.s().abs()) / 2
    }

    /// Computes coordinates unsigned distance from center
    ///
    /// See [`Self::length`] for the signed version
    #[inline]
    #[must_use]
    pub const fn ulength(self) -> u32 {
        (self.q.unsigned_abs() + self.r.unsigned_abs() + self.s().unsigned_abs()) / 2
    }

    /// Computes coordinates signed distance from another hex
    ///
    /// See [`Self::udistance`] for the unsigned version
    #[inline]
    #[must_use]
    pub const fn distance(self, other: Self) -> i32 {
        self.const_sub(other).length()
    }

    /// Computes coordinates unsigned distance from another hex
    ///
    /// See [`Self::distance`] for the signed version
    #[inline]
    #[must_use]
    pub const fn udistance(self, other: Self) -> u32 {
        self.const_sub(other).ulength()
    }

    /// Get a neighbor by index
    /// For order and direction see [`Self::DIRECTIONS`]
    ///
    /// #Panics
    /// Panics if index is 6 or higher
    #[inline]
    #[must_use]
    pub fn neighbor(self, index: usize) -> Self {
        self + Self::DIRECTIONS[index]
    }

    /// Get all neigbors of this hex
    /// For order and direction see [`Self::DIRECTIONS`]
    #[inline]
    #[must_use]
    pub fn neighbors(self) -> [Self; 6] {
        Self::DIRECTIONS.map(|h| self + h)
    }

    /// Get a diagonal neighbor by index
    /// For order and direction see [`Self::DIAGONALS`]
    ///
    /// #Panics
    /// Panics if index is 6 or higher
    #[inline]
    #[must_use]
    pub fn diagonal_neighbor(self, index: usize) -> Self {
        self + Self::DIAGONALS[index]
    }

    /// Get all diagonal neigbors of this hex
    /// For order and direction see [`Self::DIAGONALS`]
    #[inline]
    #[must_use]
    pub fn diagonal_neighbors(self) -> [Self; 6] {
        Self::DIAGONALS.map(|h| self + h)
    }

    /// Rotate hex counter clockwise
    #[inline]
    #[must_use]
    pub const fn rotate_left(self) -> Self {
        Self {
            q: -self.s(),
            r: -self.q,
        }
    }

    /// Rotate hex counter clockwise around `center`
    #[inline]
    #[must_use]
    pub const fn rotate_left_around(self, center: Self) -> Self {
        self.const_sub(center).rotate_left().const_add(center)
    }

    /// Rotate hex clockwise
    #[inline]
    #[must_use]
    pub const fn rotate_right(self) -> Self {
        Self {
            q: -self.r,
            r: -self.s(),
        }
    }

    /// Rotate hex clockwise around `center`
    #[inline]
    #[must_use]
    pub const fn rotate_right_around(self, center: Self) -> Self {
        self.const_sub(center).rotate_right().const_add(center)
    }

    /// Reflect hex over `center`
    ///
    /// The same as [`Self::const_neg`] but not over [`Hex::ZERO`]
    #[inline]
    #[must_use]
    pub const fn reflect_over(self, center: Self) -> Self {
        self.const_sub(center).const_neg().const_add(center)
    }

    /// Reflect hex across the `q` axis over [`Hex::ZERO`]
    #[inline]
    #[must_use]
    pub const fn reflect_q(self) -> Self {
        Self {
            q: self.q,
            r: self.s(),
        }
    }

    /// Reflect hex across the `q` axis over `center`
    #[inline]
    #[must_use]
    pub const fn reflect_q_over(self, center: Self) -> Self {
        self.const_sub(center).reflect_q().const_add(center)
    }

    /// Reflect hex across the `r` axis over [`Hex::ZERO`]
    #[inline]
    #[must_use]
    pub const fn reflect_r(self) -> Self {
        Self {
            q: self.s(),
            r: self.r,
        }
    }

    /// Reflect hex across the `r` axis over `center`
    #[inline]
    #[must_use]
    pub const fn reflect_r_over(self, center: Self) -> Self {
        self.const_sub(center).reflect_r().const_add(center)
    }

    /// Reflect hex across the `s` axis over [`Hex::ZERO`]
    #[inline]
    #[must_use]
    pub const fn reflect_s(self) -> Self {
        Self {
            q: self.r,
            r: self.q,
        }
    }

    /// Reflect hex across the `s` axis over `center`
    #[inline]
    #[must_use]
    pub const fn reflect_s_over(self, center: Self) -> Self {
        self.const_sub(center).reflect_s().const_add(center)
    }
}

impl Add<Self> for Hex {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            q: self.q.add(rhs.q),
            r: self.r.add(rhs.r),
        }
    }
}

impl AddAssign<Self> for Hex {
    fn add_assign(&mut self, rhs: Self) {
        self.q.add_assign(rhs.q);
        self.r.add_assign(rhs.r);
    }
}

impl Sub<Self> for Hex {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            q: self.q.sub(rhs.q),
            r: self.r.sub(rhs.r),
        }
    }
}

impl SubAssign<Self> for Hex {
    fn sub_assign(&mut self, rhs: Self) {
        self.q.sub_assign(rhs.q);
        self.r.sub_assign(rhs.r);
    }
}

impl Mul<i32> for Hex {
    type Output = Self;

    fn mul(self, rhs: i32) -> Self::Output {
        Self {
            q: self.q.mul(rhs),
            r: self.r.mul(rhs),
        }
    }
}

impl Mul<Hex> for i32 {
    type Output = Hex;

    fn mul(self, rhs: Hex) -> Self::Output {
        Hex {
            q: self.mul(rhs.q),
            r: self.mul(rhs.r),
        }
    }
}

impl MulAssign<i32> for Hex {
    fn mul_assign(&mut self, rhs: i32) {
        self.q.mul_assign(rhs);
        self.r.mul_assign(rhs);
    }
}

impl Neg for Hex {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            q: self.q.neg(),
            r: self.r.neg(),
        }
    }
}

impl From<FHex> for Hex {
    fn from(value: FHex) -> Self {
        value.round()
    }
}

impl From<(i32, i32)> for Hex {
    fn from((q, r): (i32, i32)) -> Self {
        Self { q, r }
    }
}

impl From<[i32; 2]> for Hex {
    fn from([q, r]: [i32; 2]) -> Self {
        Self { q, r }
    }
}

impl Display for Hex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}, {}]", self.q, self.r)
    }
}

#[cfg(test)]
mod tests {
    use super::Hex;

    #[test]
    fn addition() {
        assert_eq!(Hex::ZERO + Hex::ZERO, Hex::ZERO);
        assert_eq!(Hex::ZERO + Hex::ONE, Hex::ONE);
        assert_eq!(Hex::ONE + Hex::ONE, Hex::new(2, 2));
        assert_eq!(Hex::ONE + Hex::new(3, 4), Hex::new(4, 5));

        assert_eq!(Hex::ZERO.const_add(Hex::ZERO), Hex::ZERO);
        assert_eq!(Hex::ZERO.const_add(Hex::ONE), Hex::ONE);
        assert_eq!(Hex::ONE.const_add(Hex::ONE), Hex::new(2, 2));
        assert_eq!(Hex::ONE.const_add(Hex::new(3, 4)), Hex::new(4, 5));
    }

    #[test]
    fn subtraction() {
        assert_eq!(Hex::ZERO - Hex::ZERO, Hex::ZERO);
        assert_eq!(Hex::ONE - Hex::ZERO, Hex::ONE);
        assert_eq!(Hex::ONE - Hex::ONE, Hex::ZERO);
        assert_eq!(Hex::ONE - Hex::new(2, 2), Hex::new(-1, -1));
        assert_eq!(Hex::ONE - Hex::new(4, 5), Hex::new(-3, -4));

        assert_eq!(Hex::ZERO.const_sub(Hex::ZERO), Hex::ZERO);
        assert_eq!(Hex::ONE.const_sub(Hex::ZERO), Hex::ONE);
        assert_eq!(Hex::ONE.const_sub(Hex::ONE), Hex::ZERO);
        assert_eq!(Hex::ONE.const_sub(Hex::new(2, 2)), Hex::new(-1, -1));
        assert_eq!(Hex::ONE.const_sub(Hex::new(4, 5)), Hex::new(-3, -4));
    }

    #[test]
    fn multiplication() {
        assert_eq!(Hex::ONE * 0, Hex::ZERO);
        assert_eq!(Hex::ONE * 1, Hex::ONE);
        assert_eq!(Hex::new(2, 2) * 1, Hex::new(2, 2));
        assert_eq!(1 * Hex::new(5, 6), Hex::new(5, 6));
        assert_eq!(Hex::new(2, 3) * 2, Hex::new(4, 6));

        assert_eq!(Hex::ONE.const_mul(0), Hex::ZERO);
        assert_eq!(Hex::ONE.const_mul(1), Hex::ONE);
        assert_eq!(Hex::new(2, 2).const_mul(1), Hex::new(2, 2));
        assert_eq!(Hex::new(2, 3).const_mul(2), Hex::new(4, 6));
    }

    #[test]
    fn negation() {
        assert_eq!(-Hex::ZERO, Hex::ZERO);
        assert_eq!(-Hex::ONE, Hex::new(-1, -1));
        assert_eq!(-(-Hex::ONE), Hex::ONE);

        assert_eq!(Hex::ZERO.const_neg(), Hex::ZERO);
        assert_eq!(Hex::ONE.const_neg(), Hex::new(-1, -1));
        assert_eq!((Hex::ONE.const_neg()).const_neg(), Hex::ONE);
    }

    #[test]
    fn length() {
        assert_eq!(Hex::ZERO.length(), 0);
        assert_eq!(Hex::ZERO.ulength(), 0);
        assert_eq!(Hex::ONE.length(), 2);
        assert_eq!(Hex::ONE.ulength(), 2);
    }

    #[test]
    fn distance() {
        assert_eq!(Hex::ZERO.distance(Hex::ZERO), 0);
        assert_eq!(Hex::ZERO.udistance(Hex::ZERO), 0);
        assert_eq!(Hex::ONE.distance(Hex::ONE), 0);
        assert_eq!(Hex::ONE.udistance(Hex::ONE), 0);
        assert_eq!(Hex::ONE.distance(Hex::ZERO), 2);
        assert_eq!(Hex::ONE.udistance(Hex::ZERO), 2);
    }

    #[test]
    fn neigbors() {
        assert_eq!(Hex::ZERO.neighbor(0), Hex::DIRECTIONS[0]);
        assert_eq!(Hex::ZERO.neighbor(1), Hex::DIRECTIONS[1]);
        assert_eq!(Hex::ZERO.neighbor(1).neighbor(4), Hex::ZERO);

        assert_eq!(
            Hex::ONE.neighbors(),
            [
                Hex::new(2, 0),
                Hex::new(2, 1),
                Hex::new(1, 2),
                Hex::new(0, 2),
                Hex::new(0, 1),
                Hex::new(1, 0)
            ]
        );
    }

    #[test]
    fn diagonals() {
        assert_eq!(Hex::ZERO.diagonal_neighbor(0), Hex::DIAGONALS[0]);
        assert_eq!(Hex::ZERO.diagonal_neighbor(1), Hex::DIAGONALS[1]);
        assert_eq!(
            Hex::ZERO.diagonal_neighbor(1).diagonal_neighbor(4),
            Hex::ZERO
        );

        assert_eq!(
            Hex::ONE.diagonal_neighbors(),
            [
                Hex::new(3, 0),
                Hex::new(2, 2),
                Hex::new(0, 3),
                Hex::new(-1, 2),
                Hex::new(0, 0),
                Hex::new(2, -1)
            ]
        );
    }

    #[test]
    fn reflection() {
        assert_eq!(Hex::ONE.reflect_over(Hex::ZERO), Hex::new(-1, -1));
        assert_eq!(Hex::new(2, 1).reflect_over(Hex::ONE), Hex::new(0, 1));

        assert_eq!(Hex::new(2, 1).reflect_q(), Hex::new(2, -3));
        assert_eq!(Hex::new(2, 1).reflect_q_over(Hex::ZERO), Hex::new(2, -3));
        assert_eq!(Hex::new(2, 1).reflect_q_over(Hex::ONE), Hex::new(2, 0));

        assert_eq!(Hex::new(2, 1).reflect_r(), Hex::new(-3, 1));
        assert_eq!(Hex::new(2, 1).reflect_r_over(Hex::ZERO), Hex::new(-3, 1));
        assert_eq!(Hex::new(2, 1).reflect_r_over(Hex::ONE), Hex::new(0, 1));

        assert_eq!(Hex::new(2, 1).reflect_s(), Hex::new(1, 2));
        assert_eq!(Hex::new(2, 1).reflect_s_over(Hex::ZERO), Hex::new(1, 2));
        assert_eq!(Hex::new(2, 1).reflect_s_over(Hex::ONE), Hex::new(1, 2));
    }
}
