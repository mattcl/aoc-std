use xxhash_rust::xxh3::xxh3_64;

/// Convert a [&str] to a [u64] using xxh3 under the hood.
///
/// This is intended for simplifying handling of data where taking ownership of
/// full strings is undesirable and/or we want to improve hash performance by
/// not having to repeatedly hash strings.
#[inline]
pub fn str_to_u64(s: &str) -> u64 {
    xxh3_64(s.as_bytes())
}
