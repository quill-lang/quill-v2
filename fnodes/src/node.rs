//! Defines core functionality of individual Feather nodes.
//! Feather expressions are comprised of individual nodes.
//! Nodes may have children, which are more children.

use std::{
    any::Any,
    collections::{HashMap, HashSet},
    fmt::Debug,
    marker::PhantomData,
};

use fcommon::{Span, Str};

use crate::{deserialise::*, DefinitionContents, ModuleContents, SexprParser};
use crate::{expr::ExprContents, s_expr::*};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeId(u32);

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
    pub contents: C,
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
    pub fn new(id: NodeId, span: Span, contents: C) -> Self {
        Self { id, span, contents }
    }

    /// Get the node's ID.
    pub fn id(&self) -> NodeId {
        self.id
    }

    /// Get the node's span.
    pub fn span(&self) -> Span {
        self.span.clone()
    }
}

/// Nodes may have optional node info.
/// This is stored in a node info container.
#[derive(PartialEq, Eq)]
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

    /// Assumes that the given ID is of a node of type `C`.
    /// See [`HashMap::insert`].
    pub fn insert_from_id(&mut self, id: NodeId, value: T) -> Option<T> {
        self.map.insert(id, value)
    }

    /// See [`HashMap::get`].
    pub fn get(&self, node: &Node<C>) -> Option<&T> {
        self.map.get(&node.id)
    }

    /// Assumes that the given ID is of a node of type `C`.
    /// See [`HashMap::get`].
    pub fn get_from_id(&self, id: NodeId) -> Option<&T> {
        self.map.get(&id)
    }

    /// See [`HashMap::get_mut`].
    pub fn get_mut(&mut self, node: &Node<C>) -> Option<&mut T> {
        self.map.get_mut(&node.id)
    }

    /// Assumes that the given ID is of a node of type `C`.
    /// See [`HashMap::get_mut`].
    pub fn get_mut_from_id(&mut self, id: NodeId) -> Option<&mut T> {
        self.map.get_mut(&id)
    }

    pub fn keys(&self) -> std::collections::hash_map::Keys<NodeId, T> {
        self.map.keys()
    }

    pub fn iter(&self) -> std::collections::hash_map::Iter<NodeId, T> {
        self.map.iter()
    }

    /// Constructs a node info container that contains the information from both input containers.
    pub fn union(mut self, other: Self) -> Self {
        self.map.extend(other.map);
        self
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
    ) -> Box<
        dyn FnOnce(
            &mut SexprParseContext,
            &dyn SexprParser,
            SexprNode,
        ) -> Result<Box<dyn Any>, ParseError>,
    >;
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
    ) -> Box<
        dyn FnOnce(
            &mut SexprParseContext,
            &dyn SexprParser,
            SexprNode,
        ) -> Result<Box<dyn Any>, ParseError>,
    > {
        Box::new(
            |ctx: &mut SexprParseContext, db: &dyn SexprParser, value_node: SexprNode| {
                //let value_node_span = value_node.span.clone();
                ListParsableWrapper::<T>::parse(ctx, db, value_node)
                    .map(|x| Box::new(x.0) as Box<dyn Any>)
            },
        )
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

/// Generates unique deterministic identifiers for nodes.
/// One should be associated with each top-level object that
/// requires nodes.
/// Nodes are compared solely using their IDs, so it is *not* sound
/// to compare nodes associated with different generators.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct NodeIdGenerator {
    /// The node ID to be assigned to the next node that is created.
    next_node_id: NodeId,
}

impl Default for NodeIdGenerator {
    fn default() -> Self {
        Self {
            next_node_id: NodeId(0),
        }
    }
}

impl NodeIdGenerator {
    /// Generate a new ID that is unique among IDs generated by this generator.
    pub fn gen(&mut self) -> NodeId {
        let result = self.next_node_id;
        self.next_node_id.0 += 1;
        result
    }
}

/// Contains mutable references to all node info containers known about during a parse operation.
/// The containers will be filled with all the info found in S-expressions.
#[derive(Default)]
pub struct SexprParseContext<'a> {
    pub node_id_gen: NodeIdGenerator,

    /// Containers to be filled with expression node info.
    expr_infos: Vec<&'a mut dyn AbstractNodeInfoContainer<ExprContents>>,
    /// A list of all of the keywords for expression infos that were ignored (see [`Self::process_expr_info`]).
    expr_ignored_keywords: HashSet<String>,

    /// Containers to be filled with name node info.
    name_infos: Vec<&'a mut dyn AbstractNodeInfoContainer<Str>>,
    /// A list of all of the keywords for name infos that were ignored (see [`Self::process_name_info`]).
    name_ignored_keywords: HashSet<String>,

    /// Containers to be filled with module node info.
    module_infos: Vec<&'a mut dyn AbstractNodeInfoContainer<ModuleContents>>,
    /// A list of all of the keywords for module infos that were ignored (see [`Self::process_module_info`]).
    module_ignored_keywords: HashSet<String>,

    /// Containers to be filled with definition node info.
    def_infos: Vec<&'a mut dyn AbstractNodeInfoContainer<DefinitionContents>>,
    /// A list of all of the keywords for definition infos that were ignored (see [`Self::process_def_info`]).
    def_ignored_keywords: HashSet<String>,
}

macro_rules! generate_process_functions {
    ($t:ty, $register_fname:ident, $process_fname:ident, $infos:ident, $kwds:ident) => {
        /// Passes in a reference to a node info container.
        pub fn $register_fname<T>(&mut self, info: &'a mut NodeInfoContainer<$t, T>)
        where
            T: SexprListParsable + 'static,
        {
            // Check to see if this keyword has already been used for an expression info.
            for expr_info in &self.$infos {
                if info.keyword() == expr_info.keyword() {
                    panic!("keyword {} used for two different infos", info.keyword())
                }
            }

            self.$infos.push(info);
        }

        /// Call this with an info node to be parsed.
        /// If its leading keyword matched any info registered with [`Self::register_expr_info`] (for example),
        /// it will be processed.
        /// Otherwise, it will be *ignored*, and the ignored keyword will be appended to the list of ignored
        /// keywords.
        pub(crate) fn $process_fname(
            &mut self,
            db: &dyn SexprParser,
            node: &Node<$t>,
            value_node: SexprNode,
        ) -> Result<(), ParseError> {
            let keyword = find_keyword_from_list(&value_node)?;

            let value_node_span = value_node.span.clone();

            // This is a bit of lifetime hacking to make it possible to dynamically
            // insert arbitrary amounts of AbstractNodeInfoContainers.
            // We find the correct info once in order to get the parse function, then
            // we find it again mutably so that we can emplace the new parsed
            // value into its backing map.

            let info = self.$infos.iter().find(|info| info.keyword() == keyword);
            let value = if let Some(info) = info {
                info.parse_node()(self, db, value_node)?
            } else {
                // Ignore the info.
                self.$kwds.insert(keyword.clone());
                return Ok(());
            };

            let info = self
                .$infos
                .iter_mut()
                .find(|info| info.keyword() == keyword);
            if let Some(info) = info {
                info.insert_value(node, value_node_span, value)
            } else {
                panic!(
                    "failed to find info for keyword '{}' a second time",
                    keyword
                );
            }
        }
    };
}

impl<'a> SexprParseContext<'a> {
    generate_process_functions!(
        ExprContents,
        register_expr_info,
        process_expr_info,
        expr_infos,
        expr_ignored_keywords
    );
    generate_process_functions!(
        Str,
        register_name_info,
        process_name_info,
        name_infos,
        name_ignored_keywords
    );
    generate_process_functions!(
        ModuleContents,
        register_module_info,
        process_module_info,
        module_infos,
        module_ignored_keywords
    );
    generate_process_functions!(
        DefinitionContents,
        register_def_info,
        process_def_info,
        def_infos,
        def_ignored_keywords
    );

    /// Relinquish the borrows of the node info containers.
    /// Returns the list of expr info keywords that were ignored and not processed.
    pub fn finish(self) -> SexprParseContextResult {
        SexprParseContextResult {
            node_id_gen: self.node_id_gen,
            expr_ignored_keywords: self.expr_ignored_keywords,
            name_ignored_keywords: self.name_ignored_keywords,
        }
    }
}

pub struct SexprParseContextResult {
    /// A node ID generator associated with the nodes generated in this parse operation.
    pub node_id_gen: NodeIdGenerator,
    /// A list of all of the keywords for expression infos that were ignored.
    pub expr_ignored_keywords: HashSet<String>,
    /// A list of all of the keywords for name infos that were ignored.
    pub name_ignored_keywords: HashSet<String>,
}
