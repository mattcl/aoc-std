use std::collections::VecDeque;

use num::{Bounded, Num};

/// Return a minimum distance matrix compatible with [floyd_warshall].
///
/// This will be initialized with a zero diagonal and `T::MAX / 3` (infinite)
/// values in all other cells.
pub fn make_fw_dist_matrix<T>(size: usize) -> Vec<Vec<T>>
where
    T: Num + Bounded + Copy,
{
    // The price of generalizing, I guess.
    let inf = T::max_value() / (T::one() + T::one() + T::one());
    let mut out = vec![vec![inf; size]; size];

    // any node to itself is zero
    #[allow(clippy::needless_range_loop)]
    for i in 0..size {
        out[i][i] = T::zero();
    }

    out
}

/// Return a vertex matrix compatible with [floyd_warshall].
///
/// This will be initialized with a identity (i) diagonal and `T::MAX`
/// (infinite) values in all other cells.
///
/// Afterward, you will still need to assign `[u][v] = u` for  every edge
/// `(u, v)`.
pub fn make_fw_vertex_matrix(size: usize) -> Vec<Vec<usize>> {
    // The price of generalizing, I guess.
    let mut out = vec![vec![usize::MAX; size]; size];

    // any node to itself is zero
    #[allow(clippy::needless_range_loop)]
    for i in 0..size {
        out[i][i] = i;
    }

    out
}

/// Given an N x N matrix (`Vec<Vec<>>`), apply Floyd-Warshall to determine the
/// minimun distances.
///
/// https://en.wikipedia.org/wiki/Floyd%E2%80%93Warshall_algorithm
///
/// Runtime is `O(n^3)`, as expected.
pub fn floyd_warshall<T>(path_matrix: &mut [Vec<T>])
where
    T: Num + Ord + Copy,
{
    let len = path_matrix[0].len();
    for k in 0..len {
        for i in 0..len {
            for j in 0..len {
                path_matrix[i][j] = path_matrix[i][j].min(path_matrix[i][k] + path_matrix[k][j]);
            }
        }
    }
}

/// Given an `path_matrix` (`Vec<Vec<>>`) and `vertex_matrix, apply
/// Floyd-Warshall to determine the minimun distances and enable path
/// reconstruction.
///
/// https://en.wikipedia.org/wiki/Floyd%E2%80%93Warshall_algorithm
pub fn floyd_warshall_with_path<T>(path_matrix: &mut [Vec<T>], vertex_matrix: &mut [Vec<usize>])
where
    T: Num + Ord + Copy,
{
    let len = path_matrix[0].len();
    for k in 0..len {
        for i in 0..len {
            for j in 0..len {
                let memo = path_matrix[i][k] + path_matrix[k][j];
                if path_matrix[i][j] > memo {
                    path_matrix[i][j] = memo;
                    vertex_matrix[i][j] = vertex_matrix[k][j];
                }
            }
        }
    }
}

pub fn reconstruct_path(
    start: usize,
    end: usize,
    vertex_matrix: &[Vec<usize>],
) -> Option<VecDeque<usize>> {
    let mut p = VecDeque::default();
    let mut v = end;

    if vertex_matrix[start][v] > vertex_matrix[0].len() {
        return None;
    }

    p.push_front(v);

    while start != v {
        v = vertex_matrix[start][v];
        p.push_front(v);
    }

    Some(p)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn path_matrix_init() {
        let inf = i64::MAX / 3;
        let expected = vec![vec![0, inf, inf], vec![inf, 0, inf], vec![inf, inf, 0]];

        assert_eq!(make_fw_dist_matrix::<i64>(3), expected);
    }

    #[test]
    fn vertex_matrix_init() {
        let inf = usize::MAX;
        let expected = vec![vec![0, inf, inf], vec![inf, 1, inf], vec![inf, inf, 2]];

        assert_eq!(make_fw_vertex_matrix(3), expected);
    }

    #[test]
    fn floyd_warshall_ok() {
        let inf = i64::MAX / 3;
        let mut input = vec![
            vec![0, inf, -2, inf],
            vec![4, 0, 3, inf],
            vec![inf, inf, 0, 2],
            vec![inf, -1, inf, 0],
        ];

        let expected = vec![
            vec![0, -1, -2, 0],
            vec![4, 0, 2, 4],
            vec![5, 1, 0, 2],
            vec![3, -1, 1, 0],
        ];

        floyd_warshall(&mut input);

        assert_eq!(input, expected);
    }

    #[test]
    fn floyd_warshall_with_path_ok() {
        let inf = i64::MAX / 3;
        let mut input = vec![
            vec![0, inf, -2, inf],
            vec![4, 0, 3, inf],
            vec![inf, inf, 0, 2],
            vec![inf, -1, inf, 0],
        ];

        let mut vertex = make_fw_vertex_matrix(4);

        let expected = vec![
            vec![0, -1, -2, 0],
            vec![4, 0, 2, 4],
            vec![5, 1, 0, 2],
            vec![3, -1, 1, 0],
        ];

        floyd_warshall_with_path(&mut input, &mut vertex);

        assert_eq!(input, expected);
    }
}
