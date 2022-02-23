//! Defines core functionality of individual Feather nodes.
//! Feather expressions are comprised of individual nodes.
//! Nodes may have children, which are more children.

use std::{
    collections::HashMap,
    marker::PhantomData,
    sync::atomic::{AtomicU64, Ordering},
};

use crate::deserialise::*;
use crate::s_expr::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct NodeId(u64);
static ID_COUNTER: AtomicU64 = AtomicU64::new(0);

impl NodeId {
    /// Generate a new unique node identifier.
    fn new() -> NodeId {
        NodeId(ID_COUNTER.fetch_add(1, Ordering::Relaxed))
    }
}

impl Default for NodeId {
    fn default() -> Self {
        Self::new()
    }
}

/// A [`Node`] is Feather information that may be manipulated, such as expressions.
/// Things like locations, which should not be altered by the Feather compiler,
/// are not considered nodes, even if they are encoded as such in S-expressions.
///
/// `C` is the node's contents.
pub struct Node<C> {
    /// A unique identifier for this node.
    id: NodeId,
    /// The span at which the node resides in the S-expression.
    span: Span,
    /// The actual contents for this node.
    contents: C,
}

impl<C> PartialEq for Node<C> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<C> Eq for Node<C> {}

/// Nodes may have optional node info.
/// This optional info must implement the NodeInfo trait.
///
/// Node info must be a list S-expression beginning with a specific keyword.
pub trait NodeInfo: SexprListParsable {}

/// Nodes may have optional node info.
/// This is stored in a node info container.
pub struct NodeInfoContainer<C, T> {
    map: HashMap<NodeId, T>,
    /// We will enforce that only nodes of type `Node<C>` will have entries in this map.
    /// However, this cannot be guaranteed simply by the type, so we need a phantom data.
    phantom: PhantomData<C>,
}

impl<C, T> NodeInfoContainer<C, T> {
    pub fn new() -> Self {
        NodeInfoContainer {
            map: HashMap::new(),
            phantom: PhantomData,
        }
    }

    /// See [`HashMap::insert`].
    pub fn insert(&mut self, node: &Node<C>, value: T) -> Option<T> {
        self.map.insert(node.id, value)
    }

    /// See [`HashMap::get`].
    pub fn get(&self, node: &Node<C>) -> Option<&T> {
        self.map.get(&node.id)
    }

    /// See [`HashMap::get_mut`].
    pub fn get_mut(&mut self, node: &Node<C>) -> Option<&mut T> {
        self.map.get_mut(&node.id)
    }
}

impl<C, T> Default for NodeInfoContainer<C, T> {
    fn default() -> Self {
        Self::new()
    }
}
