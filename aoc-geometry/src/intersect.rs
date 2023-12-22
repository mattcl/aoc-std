/// Indicates that the intersection can be computed between two geometries.
pub trait Intersect<Rhs = Self> {
    type Intersection;

    /// Returns an intersection between ourself and `Rhs` if one exists.
    ///
    /// Returns [None] if no intersection.
    fn intersection(&self, other: &Rhs) -> Option<Self::Intersection>;

    /// Returns true if `self` intersects `other`.
    fn intersects(&self, other: &Rhs) -> bool {
        // May want to override this definition if the construction of the
        // intersection is costly
        self.intersection(other).is_some()
    }
}
