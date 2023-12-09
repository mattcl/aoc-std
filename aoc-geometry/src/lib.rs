//! This module contains structs repreesnting different geometries.
//!
//! These primarily include points and bounds.
pub mod bound;
pub mod intersect;
pub mod interval;
pub mod pascals_triangle;
pub mod point;
pub mod rect;

// re-exports
pub use bound::{AocBound, Bound2D, Bound3D, BoundND};
pub use intersect::Intersect;
pub use interval::{Interval, IntervalPartition};
pub use pascals_triangle::PascalsTriangle;
pub use point::{AocPoint, Location, Point2D, Point3D, PointND};
pub use rect::Rectangle;
