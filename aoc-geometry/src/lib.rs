//! This module contains structs repreesnting different geometries.
//!
//! These primarily include points and bounds.
pub mod bound;
pub mod point;

// re-exports
pub use bound::{AocBound, Bound2D, Bound3D, BoundND};
pub use point::{AocPoint, Location, Point2D, Point3D, PointND};
