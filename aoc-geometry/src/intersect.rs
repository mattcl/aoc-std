/// Indicates that the intersection can be computed between two geometries.
pub trait Intersect<Rhs = Self> {
    type Intersection;

    /// Returns an intersection between ourself and `Rhs` if one exists.
    ///
    /// Returns [None] if no intersection.
    fn intersection(&self, other: &Rhs) -> Option<Self::Intersection>;
}
