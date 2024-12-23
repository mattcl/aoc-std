use indexmap::{IndexMap, IndexSet};
use rustc_hash::FxHasher;
use std::hash::BuildHasherDefault;

// re-export
pub use indexmap;

/// An IndexMap with FxHasher
pub type FxIndexMap<K, V> = IndexMap<K, V, BuildHasherDefault<FxHasher>>;

/// An IndexSet with FxHasher
pub type FxIndexSet<K> = IndexSet<K, BuildHasherDefault<FxHasher>>;

// Our stuff
pub mod bitset;
pub mod bucket_queue;
pub mod char_set;
pub mod grid;
pub mod int_vec;
pub mod point_grid;

pub use bitset::BitSet;
pub use bucket_queue::{BucketQueue, DefaultBucketQueue};
pub use char_set::CharSet;
pub use grid::{CharGrid, DigitGrid, Grid};
pub use int_vec::{IntVec, IntVecError};
