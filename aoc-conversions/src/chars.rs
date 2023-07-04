/// Converts an ascii alpha char to u8.
///
/// The conversion is as follows:
///
///   `a..=z -> 0..=25`
///
///   `A..=Z -> 26..=51`
///
/// This is unchecked and does not verify the char is ascii. That should be
/// checked elsewhere.
#[inline]
pub fn ascii_alpha_to_num(ch: char) -> u8 {
    if ch.is_lowercase() {
        (ch as u8) - b'a'
    } else {
        (ch as u8) - b'A' + 26
    }
}

/// Converts a lowercase ascii alpha char to u8.
///
/// The conversion is as follows:
///
///   `a..=z -> 0..=25`
///
/// This is unchecked and does not verify the char is ascii or lowercase. That
/// should be checked elsewhere.
#[inline]
pub fn ascii_lowercase_alpha_to_num(ch: char) -> u8 {
    (ch as u8) - b'a'
}

/// Converts a u8 produced by [ascii_alpha_to_num] back to a char.
///
/// The conversion is as follows:
///
///   `0..=25 -> a..=z`
///
///   `26..=51 -> A..=Z`
///
/// This is unchecked and does not verify the value is valid. That should be
/// checked elsewhere.
#[inline]
pub fn num_to_ascii_alpha(num: u8) -> char {
    if num > 25 {
        (num + b'A' - 26) as char
    } else {
        (num + b'a') as char
    }
}

/// Converts a u8 produced by [ascii_lowercase_alpha_to_num] back to a char.
///
/// The conversion is as follows:
///
///   `0..=25 -> a..=z`
///
/// This is unchecked and does not verify the value is valid. That should be
/// checked elsewhere.
#[inline]
pub fn num_to_lowercase_ascii_alpha(num: u8) -> char {
    (num + b'a') as char
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn to_num() {
        for (idx, ch) in ('a'..'z').enumerate() {
            assert_eq!(ascii_alpha_to_num(ch), idx as u8);
            assert_eq!(ascii_lowercase_alpha_to_num(ch), idx as u8);
        }

        for (idx, ch) in ('A'..'Z').enumerate() {
            assert_eq!(ascii_alpha_to_num(ch), idx as u8 + 26);
        }
    }

    #[test]
    fn to_char() {
        for (idx, ch) in ('a'..'z').enumerate() {
            assert_eq!(num_to_ascii_alpha(idx as u8), ch);
            assert_eq!(num_to_lowercase_ascii_alpha(idx as u8), ch);
        }

        for (idx, ch) in ('A'..'Z').enumerate() {
            assert_eq!(num_to_ascii_alpha(idx as u8 + 26), ch);
        }
    }
}
