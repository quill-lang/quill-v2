use std::collections::BTreeMap;

use fcommon::{Dr, Source, Span};

use crate::pre_lex::PreToken;

/// A token in the source file. One or more of these is created for each pre-token,
/// except non-documentation comment pre-tokens, which are removed.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Token {
    Lexical { text: String },
    Operator { text: String, precedence: i32 },
    LParen,
    RParen,
}

impl Token {
    /// Gets the amount of Unicode characters in the underlying string.
    fn chars_count(&self) -> usize {
        match self {
            Token::Lexical { text } => text.chars().count(),
            Token::Operator { text, .. } => text.chars().count(),
            Token::LParen => 1,
            Token::RParen => 1,
        }
    }
}

/// Converts a stream of pre-tokens into a stream of tokens.
/// TODO: Add functionality that allows this iterator to be given operators that it can then parse.
pub struct TokenIterator<'a, I>
where
    I: Iterator<Item = (PreToken, Span)>,
{
    pre_tokens: &'a mut I,
    /// If we just parsed a pre-token, this list is filled up with the tokens that the pre-token
    /// split up into, so that we can return them later with calls to [`Iterator::next()`].
    /// The list is reversed so [`Vec::pop()`] can be used to get the next token.
    parsed_tokens_rev: Vec<(Token, Span)>,
    /// The map of known operators to this token iterator.
    /// The innermost map converts operators as strings into their precedence, an [`i32`].
    /// The outermost map tracks the size of each operator; in particular, an operator with string
    /// `s` should be stored in `operators[s.len()][s]`. This allows us to parse longer operators
    /// first, which deals with situations like favouring `++` over `+`. The structure [`BTreeMap`]
    /// is used for determinism.
    operators: BTreeMap<usize, BTreeMap<String, i32>>,
}

impl<'a, I> TokenIterator<'a, I>
where
    I: Iterator<Item = (PreToken, Span)>,
{
    fn split_pre_token(&self, text: &str, span: Span) -> Vec<(Token, Span)> {
        // Search for known operators, longest first.
        for (_, operators) in self.operators.iter().rev() {
            for (operator, precedence) in operators {
                if let Some((before, after)) = text.split_once(operator) {
                    // We found an operator.
                    return self.split_pre_token_recursive(
                        before,
                        after,
                        Token::Operator {
                            text: operator.clone(),
                            precedence: *precedence,
                        },
                        span,
                    );
                }
            }
        }

        // We didn't find any operators in this text.
        // Now search for important tokens like left and right parentheses.
        if let Some((before, after)) = text.split_once('(') {
            return self.split_pre_token_recursive(before, after, Token::LParen, span);
        } else if let Some((before, after)) = text.split_once(')') {
            return self.split_pre_token_recursive(before, after, Token::RParen, span);
        }

        // We didn't find any other tokens in this text. Treat the text as a single token.
        // TODO: Warn the user if this doesn't look like a single token.
        vec![(
            Token::Lexical {
                text: text.to_owned(),
            },
            span,
        )]
    }

    /// Splits on `before` and `after`, and concatenates the results with `token` in between.
    fn split_pre_token_recursive(
        &self,
        before: &str,
        after: &str,
        token: Token,
        span: Span,
    ) -> Vec<(Token, Span)> {
        let before_len = before.chars().count();
        let token_len = token.chars_count();
        let mut result = self.split_pre_token(before, span.start..span.start + before_len);
        result.push((
            token,
            span.start + before_len..span.start + before_len + token_len,
        ));
        result.extend(self.split_pre_token(after, span.start + before_len + token_len..span.end));
        return result;
    }
}

impl<'a, I> Iterator for TokenIterator<'a, I>
where
    I: Iterator<Item = (PreToken, Span)>,
{
    type Item = (Token, Span);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(token) = self.parsed_tokens_rev.pop() {
            Some(token)
        } else {
            // Consume and parse the next pre-token.
            if let Some((pre_token, span)) = self.pre_tokens.next() {
                match pre_token {
                    PreToken::Lexical { text } => {
                        self.parsed_tokens_rev = self.split_pre_token(&text, span);
                        self.parsed_tokens_rev.reverse();
                    }
                    PreToken::Comment { .. } => {
                        // Ignore comments that are not documentation comments.
                    }
                }
                self.next()
            } else {
                None
            }
        }
    }
}

/// A parsed item from the input stream.
pub enum Item {
    Definition {},
}

/// Parses a single item from a stream of pre-tokens.
pub fn parse_item(
    source: &Source,
    stream: &mut TokenIterator<'_, impl Iterator<Item = (PreToken, Span)>>,
) -> Dr<(Item, Span)> {
    todo!()
}
