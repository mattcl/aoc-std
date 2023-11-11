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
pub mod char_set;
pub mod grid;

pub use char_set::CharSet;
pub use grid::{CharGrid, DigitGrid, Grid};
