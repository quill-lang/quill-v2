//! Manipulates chains of successor universes.

use fnodes::universe::*;

/// Factors out the outermost sequence of [`UniverseSucc`] instances.
/// If the input is `u + k` where `k` is an integer, the return value is `(u, k)`.
pub fn to_universe_with_offset(u: &Universe) -> (&Universe, UniverseLevel) {
    if let UniverseContents::UniverseSucc(UniverseSucc(inner)) = &u.contents {
        let (univ_inner, offset_inner) = to_universe_with_offset(inner);
        (univ_inner, offset_inner + 1)
    } else {
        (u, 0)
    }
}
