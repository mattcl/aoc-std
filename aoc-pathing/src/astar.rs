//! Structs, Traits, and helpers for solving shortest path via A*.
//!
//! This is influenced by the implemenation in the pathfinding crate, but with
//! some aoc-only tweaks, like not having to deal with floating point and better
//! integration with the point/location stuff.
use std::{collections::BinaryHeap, fmt::Debug, hash::Hash};

use aoc_collections::{
    indexmap::map::Entry::{Occupied, Vacant},
    FxIndexMap,
};
use num::{Bounded, Num};
use thiserror::Error;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Error)]
pub enum AStarError {
    #[error("No path found")]
    NoPath,
}

fn path_len<N, C>(cur: usize, map: &FxIndexMap<N, (usize, C)>) -> usize
where
    N: Clone + Eq + Hash,
    C: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    if let Some((_, (next_index, _))) = map.get_index(cur) {
        1 + path_len(*next_index, map)
    } else {
        0
    }
}

fn path<N, C>(cur: usize, map: &FxIndexMap<N, (usize, C)>) -> Vec<&N> {
    let mut v = Vec::new();
    let mut cur = cur;

    while let Some((node, (next_index, _))) = map.get_index(cur) {
        v.push(node);
        cur = *next_index;
    }

    v.reverse();
    v
}

/// The result of searching for the shortest path via AStar.
///
/// This will either be `Success` or `NoPath`, depending on the result of the
/// search.
///
/// For convenience, `cost()`, `path_len()`, and `path()` are provided.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum AStarResult<N, C>
where
    N: Clone + Eq + Hash,
    C: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    Success {
        goal_index: usize,
        cost: C,
        examined_nodes: FxIndexMap<N, (usize, C)>,
    },
    NoPath {
        examined_nodes: FxIndexMap<N, (usize, C)>,
    },
}

impl<N, C> AStarResult<N, C>
where
    N: Clone + Eq + Hash,
    C: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    pub fn cost(&self) -> Result<C, AStarError> {
        match self {
            Self::Success { cost, .. } => Ok(*cost),
            _ => Err(AStarError::NoPath),
        }
    }

    pub fn path_len(&self) -> Result<usize, AStarError> {
        match self {
            Self::Success {
                goal_index,
                examined_nodes,
                ..
            } => Ok(path_len(*goal_index, examined_nodes) - 1), // we need to take 1 off because of
            // the root node
            _ => Err(AStarError::NoPath),
        }
    }

    pub fn path(&self) -> Result<Vec<&N>, AStarError> {
        match self {
            Self::Success {
                goal_index,
                examined_nodes,
                ..
            } => Ok(path(*goal_index, examined_nodes)),
            _ => Err(AStarError::NoPath),
        }
    }
}

/// Find the shortest path using AStar.
///
/// This runs until `stop` returns `true` or it has exhausted the search space,
/// at which point it returns a [AStarResult] which exposes information about
/// the shortest path, if one existed.
///
/// * `start` is the node representing the start position
/// * `edges` returns a list of edges (neighbors) for a given node paired with
///   the costs of moving to each neighbor and the heuristic value.
/// * `stop` is given the current node and returns `true` if we should stop
///    searching (we've found the desired end point).
pub fn astar<N, C, E, I, S>(start: &N, edges: &mut E, stop: &mut S) -> AStarResult<N, C>
where
    N: Clone + Eq + Hash,
    C: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
    E: FnMut(&N) -> I,
    I: IntoIterator<Item = (N, C, C)>,
    S: FnMut(&N) -> bool,
{
    let mut heap = BinaryHeap::default();
    let mut cache: FxIndexMap<N, (usize, C)> = FxIndexMap::default();

    heap.push(MinState {
        estimated_cost: C::zero(),
        cost: C::zero(),
        index: 0,
    });

    cache.insert(start.clone(), (usize::MAX, C::zero()));

    let mut goal = None;
    while let Some(MinState { cost, index, .. }) = heap.pop() {
        let edges = {
            // we can unwrap because we _know_ these exist
            let (node, &(_, c)) = cache.get_index(index).unwrap();

            if stop(node) {
                goal = Some((index, cost));
                break;
            }

            if cost > c {
                continue;
            }

            edges(node)
        };

        for (edge, move_cost, heuristic) in edges {
            let new_cost = cost + move_cost;
            let next_index = match cache.entry(edge) {
                Vacant(e) => {
                    let n = e.index();
                    e.insert((index, new_cost));
                    n
                }
                Occupied(mut e) => {
                    if e.get().1 > new_cost {
                        let n = e.index();
                        e.insert((index, new_cost));
                        n
                    } else {
                        continue;
                    }
                }
            };

            heap.push(MinState {
                estimated_cost: new_cost + heuristic,
                cost: new_cost,
                index: next_index,
            });
        }
    }

    if let Some((index, cost)) = goal {
        AStarResult::Success {
            goal_index: index,
            cost,
            examined_nodes: cache,
        }
    } else {
        AStarResult::NoPath {
            examined_nodes: cache,
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
struct MinState<N>
where
    N: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    estimated_cost: N,
    cost: N,
    index: usize,
}

impl<N> Ord for MinState<N>
where
    N: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other
            .estimated_cost
            .cmp(&self.estimated_cost)
            .then_with(|| self.cost.cmp(&other.cost))
            .then_with(|| self.index.cmp(&other.index))
    }
}

impl<N> PartialOrd for MinState<N>
where
    N: Num + Bounded + Ord + PartialOrd + Copy + Default + Hash,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
