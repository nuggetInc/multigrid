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
}
