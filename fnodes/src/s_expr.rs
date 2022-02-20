//! Feather nodes can be serialised into S-expressions.
//! This module provides functionality for both serialisation and deserialisation.

use chumsky::prelude::*;

/// This trait is implemented by nodes.
/// This allows for serialisation and deserialisation of nodes to and from S-expressions.
pub trait Node {}

/// Represents a node in a tree of S-expressions.
/// All values are stored as strings, and have no semantic meaning.
/// Nodes should not be compared for equality, so there is no PartialEq impl.
#[derive(Debug)]
enum SexprNode {
    Atom(String),
    List(Vec<SexprNode>),
}

/// Parses an S-expression.
fn sexpr_parser() -> impl Parser<char, SexprNode, Error = Simple<char>> {
    // Adapted from the JSON example <https://github.com/zesterer/chumsky/blob/master/examples/json.rs>.
    let expr = recursive(|sexpr| {
        let escape = just('\\').ignore_then(
            just('\\')
                .or(just('/'))
                .or(just('"'))
                .or(just('b').to('\x08'))
                .or(just('f').to('\x0C'))
                .or(just('n').to('\n'))
                .or(just('r').to('\r'))
                .or(just('t').to('\t')),
        );

        let string = just('"')
            .ignore_then(filter(|c| *c != '\\' && *c != '"').or(escape).repeated())
            .then_ignore(just('"'))
            .collect::<String>()
            .map(SexprNode::Atom)
            .labelled("string");

        let other_atom = filter::<_, _, Simple<char>>(|c: &char| {
            !c.is_whitespace() && !matches!(c, '(' | ')' | '"')
        })
        .repeated()
        .at_least(1)
        .map(|chars| SexprNode::Atom(chars.into_iter().collect()))
        .labelled("other_atom");

        let atom = string.or(other_atom);

        let list = sexpr
            .padded()
            .repeated()
            //.or_not()
            //.flatten()
            .map(SexprNode::List)
            .delimited_by(just('('), just(')'))
            .labelled("list");

        list.or(atom)
    });
    expr.then_ignore(end())
}

#[cfg(test)]
mod tests {
    use chumsky::Parser;

    use crate::s_expr::{sexpr_parser, SexprNode};

    #[test]
    fn atom() {
        let value = sexpr_parser().parse("123").unwrap();
        let expected = SexprNode::Atom("123".to_string());
        // We intentionally don't impl PartialEq on nodes, so we have to do this for testing.
        if format!("{:#?}", value) != format!("{:#?}", expected) {
            panic!("Got: {:#?}\n\nExpected{:#?}", value, expected);
        }
    }

    #[test]
    fn list() {
        let value = sexpr_parser().parse("(a b c)").unwrap();
        let expected = SexprNode::List(vec![
            SexprNode::Atom("a".to_string()),
            SexprNode::Atom("b".to_string()),
            SexprNode::Atom("c".to_string()),
        ]);
        if format!("{:#?}", value) != format!("{:#?}", expected) {
            panic!("Got:\n{:#?}\n\nExpected:\n{:#?}", value, expected);
        }
    }

    #[test]
    fn string() {
        let value = sexpr_parser()
            .parse(r#"("Hello, world!" "escaping\\\"")"#)
            .unwrap();
        let expected = SexprNode::List(vec![
            SexprNode::Atom("Hello, world!".to_string()),
            SexprNode::Atom("escaping\\\"".to_string()),
        ]);
        if format!("{:#?}", value) != format!("{:#?}", expected) {
            panic!("Got:\n{:#?}\n\nExpected:\n{:#?}", value, expected);
        }
    }

    #[test]
    fn hierarchy() {
        let value = sexpr_parser().parse("(a b (c d) ((e) f))").unwrap();
        let expected = SexprNode::List(vec![
            SexprNode::Atom("a".to_string()),
            SexprNode::Atom("b".to_string()),
            SexprNode::List(vec![
                SexprNode::Atom("c".to_string()),
                SexprNode::Atom("d".to_string()),
            ]),
            SexprNode::List(vec![
                SexprNode::List(vec![SexprNode::Atom("e".to_string())]),
                SexprNode::Atom("f".to_string()),
            ]),
        ]);
        if format!("{:#?}", value) != format!("{:#?}", expected) {
            panic!("Got:\n{:#?}\n\nExpected:\n{:#?}", value, expected);
        }
    }
}
