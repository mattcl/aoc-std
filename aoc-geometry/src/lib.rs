//! This module contains structs repreesnting different geometries.
//!
//! These primarily include points and bounds.
pub mod bound;
pub mod cube;
pub mod intersect;
pub mod interval;
pub mod pascals_triangle;
pub mod point;
pub mod polygon;
pub mod rect;

// re-exports
pub use bound::{AocBound, Bound2D, Bound3D, BoundND};
pub use cube::Cube;
pub use intersect::Intersect;
pub use interval::{Interval, IntervalPartition, IntervalSplit};
pub use pascals_triangle::PascalsTriangle;
pub use point::{AocPoint, Location, Point2D, Point3D, PointND};
pub use polygon::Polygon;
pub use rect::Rectangle;
