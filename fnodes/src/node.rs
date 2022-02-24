//! Defines core functionality of individual Feather nodes.
//! Feather expressions are comprised of individual nodes.
//! Nodes may have children, which are more children.

use std::{
    any::Any,
    collections::{HashMap, HashSet},
    fmt::Debug,
    marker::PhantomData,
    sync::atomic::{AtomicU64, Ordering},
};

use crate::{deserialise::*, expr::Expr};
use crate::{expr::ExprContents, s_expr::*};

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

impl<C> Debug for Node<C>
where
    C: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            write!(f, "{}@{:?}:{:#?}", self.id.0, self.span, self.contents)
        } else {
            write!(f, "{}@{:?}:{:?}", self.id.0, self.span, self.contents)
        }
    }
}

impl<C> Node<C> {
    pub fn new(span: Span, contents: C) -> Self {
        Self {
            id: NodeId::new(),
            span,
            contents,
        }
    }
}

/// Nodes may have optional node info.
/// This is stored in a node info container.
pub struct NodeInfoContainer<C, T> {
    map: HashMap<NodeId, T>,
    /// We will enforce that only nodes of type `Node<C>` will have entries in this map.
    /// However, this cannot be guaranteed simply by the type, so we need a phantom data.
    phantom: PhantomData<C>,
}

impl<C, T> Debug for NodeInfoContainer<C, T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.map, f)
    }
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

/// A node info container that doesn't care about the type its info data,
/// but only cares about the node type it can be used with.
/// All instances of this trait should just be [`NodeInfoContainer`] objects.
trait AbstractNodeInfoContainer<C> {
    /// Returns the keyword of the underlying [`SexprListParsable`].
    /// This takes `self` to make `AbstractNodeInfoContainer` object-safe.
    fn keyword(&self) -> &'static str;
    /// Parses a value node.
    ///
    /// Because of lifetime requirements, we must return a function that performs the parse.
    /// In particular, the vtable for the node info container must be resolved, so we need to
    /// borrow `self`, but the parse operation may contain sub-expressions which need to access
    /// the same container!
    ///
    /// This also means we need to use `Any`, unfortunately, because the node info inserters cannot know
    /// what type this returned function returns.
    ///
    /// We allow the somewhat absurd type complexity here because the trait is private and will only ever have a single implementation.
    #[allow(clippy::type_complexity)]
    fn parse_node(
        &self,
    ) -> Box<dyn FnOnce(&mut NodeInfoInserters, SexprNode) -> Result<Box<dyn Any>, ParseError>>;
    /// Must accept the same type as is returned by [`Self::parse_node`].
    fn insert_value(
        &mut self,
        node: &Node<C>,
        value_node_span: Span,
        value: Box<dyn Any>,
    ) -> Result<(), ParseError>;
}

impl<C, T> AbstractNodeInfoContainer<C> for NodeInfoContainer<C, T>
where
    C: 'static,
    T: SexprListParsable + Any + 'static,
{
    fn keyword(&self) -> &'static str {
        T::KEYWORD.expect("node infos must have a keyword")
    }

    fn parse_node(
        &self,
    ) -> Box<dyn FnOnce(&mut NodeInfoInserters, SexprNode) -> Result<Box<dyn Any>, ParseError>>
    {
        Box::new(|infos: &mut NodeInfoInserters, value_node: SexprNode| {
            //let value_node_span = value_node.span.clone();
            ListParsableWrapper::<T>::parse(infos, value_node)
                .map(|x| Box::new(x.0) as Box<dyn Any>)
        })
    }

    fn insert_value(
        &mut self,
        node: &Node<C>,
        value_node_span: Span,
        value: Box<dyn Any>,
    ) -> Result<(), ParseError> {
        if self
            .insert(
                node,
                *value
                    .downcast()
                    .expect("only results from parse_node should be used in insert_value"),
            )
            .is_some()
        {
            Err(ParseError {
                span: value_node_span,
                reason: ParseErrorReason::RepeatedInfo {
                    info_keyword: self.keyword(),
                },
            })
        } else {
            Ok(())
        }
    }
}

impl<C, T> Default for NodeInfoContainer<C, T> {
    fn default() -> Self {
        Self::new()
    }
}

/// Mutable references to all node info containers known about during a parse operation.
/// The containers will be filled with all the info found in S-expressions.
#[derive(Default)]
pub struct NodeInfoInserters<'a> {
    /// Containers to be filled with node info.
    expr_infos: Vec<&'a mut dyn AbstractNodeInfoContainer<ExprContents>>,
    /// A list of all of the keywords for expression infos that were ignored (see [`Self::process_expr_info`]).
    expr_ignored_keywords: HashSet<String>,
}

impl<'a> NodeInfoInserters<'a> {
    /// Passes in a reference to a node info container.
    /// When a node info
    pub fn register_expr_info<T>(&mut self, info: &'a mut NodeInfoContainer<ExprContents, T>)
    where
        T: SexprListParsable + 'static,
    {
        // Check to see if this keyword has already been used for an expression info.
        for expr_info in &self.expr_infos {
            if info.keyword() == expr_info.keyword() {
                panic!("keyword {} used for two different infos", info.keyword())
            }
        }

        self.expr_infos.push(info);
    }

    /// Call this with an expression info node to be parsed.
    /// If its leading keyword matched any expression info registered with [`Self::register_expr_info`],
    /// it will be processed.
    /// Otherwise, it will be *ignored*, and the ignored keyword will be appended to the list of ignored
    /// keywords.
    pub(crate) fn process_expr_info(
        &mut self,
        expr: &Expr,
        value_node: SexprNode,
    ) -> Result<(), ParseError> {
        // TODO: Refactor this keyword-finding block into a function
        let keyword = match &value_node.contents {
            SexprNodeContents::Atom(_) => {
                return Err(ParseError {
                    span: value_node.span,
                    reason: ParseErrorReason::ExpectedList,
                })
            }
            SexprNodeContents::List(entries) => {
                if let Some(first) = entries.first() {
                    match &first.contents {
                        SexprNodeContents::Atom(kwd) => kwd.clone(),
                        SexprNodeContents::List(_) => {
                            return Err(ParseError {
                                span: value_node.span,
                                reason: ParseErrorReason::ExpectedKeywordFoundList {
                                    expected: "<any expression info>",
                                },
                            })
                        }
                    }
                } else {
                    return Err(ParseError {
                        span: value_node.span,
                        reason: ParseErrorReason::ExpectedKeywordFoundEmpty {
                            expected: "<any expression info>",
                        },
                    });
                }
            }
        };

        let value_node_span = value_node.span.clone();

        // This is a bit of lifetime hacking to make it possible to dynamically
        // insert arbitrary amounts of AbstractNodeInfoContainers.
        // We find the correct info once in order to get the parse function, then
        // we find it again mutably so that we can emplace the new parsed
        // value into its backing map.

        let info = self
            .expr_infos
            .iter()
            .find(|info| info.keyword() == keyword);
        let value = if let Some(info) = info {
            info.parse_node()(self, value_node)?
        } else {
            // Ignore the info.
            self.expr_ignored_keywords.insert(keyword.clone());
            return Ok(());
        };

        let info = self
            .expr_infos
            .iter_mut()
            .find(|info| info.keyword() == keyword);
        if let Some(info) = info {
            info.insert_value(expr, value_node_span, value)
        } else {
            panic!(
                "failed to find info for keyword '{}' a second time",
                keyword
            );
        }
    }

    /// Relinquish the borrows of the node info containers.
    /// Returns the list of expr info keywords that were ignored and not processed.
    pub fn finish(self) -> HashSet<String> {
        self.expr_ignored_keywords
    }
}
