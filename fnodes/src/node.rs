//! Defines core functionality of individual Feather nodes.
//! Feather expressions are comprised of individual nodes.
//! Nodes may have children, which are more children.

use crate::s_expr::Node;

/// Represents a line-column pair in source code.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Location {
    /// Zero-indexed line number.
    pub line: i32,
    /// Zero-indexed column number.
    pub col: i32,
}

impl Node for Location {}
