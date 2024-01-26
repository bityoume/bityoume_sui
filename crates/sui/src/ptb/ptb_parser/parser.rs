// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use crate::ptb::{ptb::PTBCommand, ptb_parser::argument::span};

use move_command_line_common::{
    address::NumericalAddress,
    parser::{parse_u128, parse_u16, parse_u256, parse_u32, parse_u64, parse_u8, Parser, Token},
    types::TypeToken,
};
use move_core_types::identifier::Identifier;
use std::{fmt::Debug, str::FromStr};

use crate::ptb::ptb_parser::argument_token::ArgumentToken;
use anyhow::{anyhow, bail, Context, Result};

use super::{
    argument::{Argument, Span, Spanned},
    command_token::CommandToken,
    context::PTBContext,
    errors::PTBError,
};

/// A parsed PTB command consisting of the command and the parsed arguments to the command.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ParsedPTBCommand {
    pub name: CommandToken,
    pub args: Vec<Spanned<Argument>>,
}

/// The parser for PTB command arguments.
pub struct ValueParser<'a> {
    inner: Spanner<'a>,
}

/// The PTB parsing context used when parsing PTB commands. This consists of:
/// - The list of alread-parsed commands
/// - The list of errors that have occured thus far during the parsing of the command(s)
///   - NB: errors are accumulated and returned at the end of parsing, instead of eagerly.
/// - The current file and command scope which is used for error reporting.
pub struct PTBParser {
    parsed: Vec<ParsedPTBCommand>,
    errors: Vec<PTBError>,
    context: PTBContext,
}

impl PTBParser {
    /// Create a new PTB parser.
    pub fn new() -> Self {
        Self {
            parsed: vec![],
            errors: vec![],
            context: PTBContext::new(),
        }
    }

    /// Return the list of parsed commands along with any errors that were encountered during the
    /// parsing of the PTB command(s).
    pub fn finish(self) -> (Vec<ParsedPTBCommand>, Vec<PTBError>) {
        (self.parsed, self.errors)
    }

    /// Parse a single PTB command. If an error is encountered, it is added to the list of
    /// `errors`.
    pub fn parse(&mut self, mut cmd: PTBCommand) {
        let name = CommandToken::from_str(&cmd.name);
        if let Err(e) = name {
            self.errors.push(PTBError::WithSource {
                file_scope: self.context.current_file_scope().clone(),
                message: format!("Failed to parse command name: {e}"),
                span: None,
            });
            return;
        };
        let name = name.unwrap();

        match name {
            CommandToken::FileEnd => {
                let name = cmd.values.pop().unwrap();
                if let Err(e) = self.context.pop_file_scope(name) {
                    self.errors.push(e);
                }
                return;
            }
            CommandToken::FileStart => {
                let name = cmd.values.pop().unwrap();
                self.context.push_file_scope(name);
                return;
            }
            CommandToken::Publish | CommandToken::Upgrade => {
                if cmd.values.len() != 1 {
                    self.errors.push(PTBError::WithSource {
                        file_scope: self.context.current_file_scope().clone(),
                        message: format!(
                            "Invalid command -- expected 1 argument, got {}",
                            cmd.values.len()
                        ),
                        span: None,
                    });
                    return;
                }
                self.context.increment_file_command_index();
                self.parsed.push(ParsedPTBCommand {
                    name,
                    args: vec![Spanned {
                        span: Span {
                            start: 0,
                            end: cmd.values[0].len(),
                            arg_idx: 0,
                        },
                        value: Argument::String(cmd.values[0].clone()),
                    }],
                });
                return;
            }
            _ => (),
        }
        let args = cmd
            .values
            .iter()
            .enumerate()
            .map(|(i, v)| Self::parse_values(&v, i))
            .collect::<Result<Vec<_>>>()
            .map_err(|e| PTBError::WithSource {
                file_scope: self.context.current_file_scope().clone(),
                message: format!("Failed to parse arguments for '{}' command. {e}", cmd.name),
                // TODO(tzakian): Span for parse errors too!
                span: None,
            });

        // println!("args: {:#?}", args);

        self.context.increment_file_command_index();

        match args {
            Ok(args) => {
                self.parsed.push(ParsedPTBCommand {
                    name,
                    args: args.into_iter().flatten().collect(),
                });
            }
            Err(e) => self.errors.push(e),
        }
    }

    /// Parse a string to a list of values. Values are separated by whitespace.
    pub fn parse_values(s: &str, arg_idx: usize) -> Result<Vec<Spanned<Argument>>> {
        let tokens: Vec<_> = ArgumentToken::tokenize(s)?;
        let stokens = Spanner::new(tokens, arg_idx);
        let mut parser = ValueParser::new(stokens, arg_idx);
        let res = parser.parse_arguments()?;
        if let Ok((_, contents)) = parser.advance_any() {
            bail!("Expected end of token stream. Got: {}", contents)
        }
        Ok(res)
    }
}

#[macro_export]
macro_rules! sp {
    (_, $value:pat) => {
        $crate::ptb::ptb_parser::argument::Spanned { value: $value, .. }
    };
    ($loc:pat, _) => {
        $crate::ptb::ptb_parser::argument::Spanned { span: $loc, .. }
    };
    ($loc:pat, $value:pat) => {
        $crate::ptb::ptb_parser::argument::Spanned {
            span: $loc,
            value: $value,
        }
    };
}

#[macro_export]
macro_rules! bind {
    ($loc:pat, $value:pat = $rhs:expr, $err:expr) => {
        let x = $rhs;
        let loc = x.span;
        let ($loc, $value) = (loc.clone(), x.value) else {
            return $err(loc);
        };
    };
}

pub struct Spanner<'a> {
    pub span: Span,
    pub tokens: Vec<(ArgumentToken, &'a str)>,
}

impl<'a> Spanner<'a> {
    pub fn new(mut tokens: Vec<(ArgumentToken, &'a str)>, arg_idx: usize) -> Self {
        tokens.reverse();
        let span = Span {
            start: 0,
            end: 0,
            arg_idx,
        };
        Self { span, tokens }
    }

    pub fn next(&mut self) -> Option<(ArgumentToken, &'a str)> {
        if let Some((tok, contents)) = self.tokens.pop() {
            self.span.end += contents.len();
            Some((tok, contents))
        } else {
            None
        }
    }

    pub fn peek(&self) -> Option<(ArgumentToken, &'a str)> {
        self.tokens.last().copied()
    }

    pub fn end_span(&mut self) -> Span {
        let x = self.span.clone();
        self.span.start = self.span.end;
        x
    }

    pub fn curr_end(&self) -> usize {
        self.span.end
    }
}

impl<'a> Iterator for Spanner<'a> {
    type Item = (ArgumentToken, &'a str);

    fn next(&mut self) -> Option<Self::Item> {
        self.next()
    }
}

impl<'a> ValueParser<'a> {
    pub fn new(v: Spanner<'a>, arg_idx: usize) -> Self {
        Self { inner: v }
    }

    pub fn advance_any(&mut self) -> Result<(ArgumentToken, &'a str)> {
        match self.inner.next() {
            Some(tok) => Ok(tok),
            None => bail!("unexpected end of tokens"),
        }
    }

    pub fn advance(&mut self, expected_token: ArgumentToken) -> Result<&'a str> {
        let (t, contents) = self.advance_any()?;
        if t != expected_token {
            bail!("expected token {}, got {}", expected_token, t)
        }
        Ok(contents)
    }

    pub fn peek(&mut self) -> Option<(ArgumentToken, &'a str)> {
        self.inner.peek()
    }

    pub fn peek_tok(&mut self) -> Option<ArgumentToken> {
        self.inner.peek().map(|(tok, _)| tok)
    }

    pub fn parse_list<R>(
        &mut self,
        parse_list_item: impl Fn(&mut Self) -> Result<R>,
        delim: ArgumentToken,
        end_token: ArgumentToken,
        allow_trailing_delim: bool,
    ) -> Result<Vec<R>> {
        let is_end = |tok_opt: Option<ArgumentToken>| -> bool {
            tok_opt.map(|tok| tok == end_token).unwrap_or(true)
        };
        let mut v = vec![];
        while !is_end(self.peek_tok()) {
            v.push(parse_list_item(self)?);
            if is_end(self.peek_tok()) {
                break;
            }
            self.advance(delim)?;
            if is_end(self.peek_tok()) && allow_trailing_delim {
                break;
            }
        }
        Ok(v)
    }

    /// Parses a list of items separated by `delim` and terminated by `end_token`, skipping any
    /// tokens that match `skip`.
    /// This is used to parse lists of arguments, e.g. `1, 2, 3` or `1, 2, 3` where the tokenizer
    /// we're using is space-sensitive so we want to `skip` whitespace, and `delim` by ','.
    pub fn parse_list_skip<R>(
        &mut self,
        parse_list_item: impl Fn(&mut Self) -> Result<R>,
        delim: ArgumentToken,
        end_token: ArgumentToken,
        skip: ArgumentToken,
        allow_trailing_delim: bool,
    ) -> Result<Vec<R>> {
        let is_end = |parser: &mut Self| -> Result<bool> {
            while parser.peek_tok() == Some(skip) {
                parser.advance(skip)?;
            }
            let is_end = parser
                .peek_tok()
                .map(|tok| tok == end_token)
                .unwrap_or(true);

            Ok(is_end)
        };
        let mut v = vec![];

        while !is_end(self)? {
            v.push(parse_list_item(self)?);
            if is_end(self)? {
                break;
            }
            self.advance(delim)?;
            if is_end(self)? && allow_trailing_delim {
                break;
            }
        }
        Ok(v)
    }
}

pub struct ParsingErr {
    pub span: Span,
    pub message: String,
}

type ParsingResult<T> = Result<T, ParsingErr>;

impl<'a> ValueParser<'a> {
    /// Parse a list of arguments separated by whitespace.
    pub fn parse_arguments(&mut self) -> Result<Vec<Spanned<Argument>>> {
        let args = self.parse_list(
            |p| p.parse_argument_outer(),
            ArgumentToken::Whitespace,
            /* not checked */ ArgumentToken::Void,
            /* allow_trailing_delim */ true,
        )?;
        Ok(args)
    }

    /// Parse an argument. Used to keep track of the current argument index that we are at for
    /// better error reporting.
    pub fn parse_argument_outer(&mut self) -> Result<Spanned<Argument>> {
        let arg = self.parse_argument().with_context(|| {
            format!(
                "Failed to parse argument at index {}",
                self.inner.span.arg_idx
            )
        });
        // TODO: Span for parse errors too!
        arg.map(|arg| Spanned {
            span: self.inner.end_span(),
            value: arg,
        })
    }

    /// Parse a numerical address.
    fn parse_address(contents: &str) -> Result<NumericalAddress> {
        NumericalAddress::parse_str(contents)
            .map_err(|s| anyhow!("Failed to parse address '{}'. Got error: {}", contents, s))
    }

    /// Parse a single PTB argument. This is the main parsing function for PTB arguments.
    pub fn parse_argument(&mut self) -> Result<Argument> {
        use super::argument_token::ArgumentToken as Tok;
        use Argument as V;
        Ok(match self.advance_any()? {
            (Tok::Ident, "true") => V::Bool(true),
            (Tok::Ident, "false") => V::Bool(false),
            (Tok::Number, contents) if matches!(self.peek_tok(), Some(Tok::ColonColon)) => {
                let address = Self::parse_address(contents)
                    .with_context(|| format!("Unable to parse address '{contents}'"))?;
                let addr_end = self.inner.curr_end();
                self.advance(Tok::ColonColon)?;
                let module_start = self.inner.curr_end();
                let module_name = Identifier::new(
                    self.advance(Tok::Ident)
                        .with_context(|| format!("Unable to parse module name"))?,
                )
                .with_context(|| format!("Unable to parse module name"))?;
                let module_end = self.inner.curr_end();
                self.advance(Tok::ColonColon)
                    .with_context(|| format!("Missing '::' after module name"))?;
                let fn_start = self.inner.curr_end();
                let function_name = Identifier::new(
                    self.advance(Tok::Ident)
                        .with_context(|| format!("Unable to parse function name"))?,
                )?;
                let fn_end = self.inner.curr_end();
                V::ModuleAccess {
                    address: span(
                        Span {
                            start: addr_end - contents.len(),
                            end: addr_end,
                            arg_idx: self.inner.span.arg_idx,
                        },
                        address,
                    ),
                    module_name: span(
                        Span {
                            start: module_start,
                            end: module_end,
                            arg_idx: self.inner.span.arg_idx,
                        },
                        module_name,
                    ),
                    function_name: span(
                        Span {
                            start: fn_start,
                            end: fn_end,
                            arg_idx: self.inner.span.arg_idx,
                        },
                        function_name,
                    ),
                }
            }
            (Tok::Number, contents) => {
                let num = u64::from_str(contents).context("Invalid number")?;
                V::U64(num)
            }
            (Tok::NumberTyped, contents) => {
                if let Some(s) = contents.strip_suffix("u8") {
                    let (u, _) = parse_u8(s)?;
                    V::U8(u)
                } else if let Some(s) = contents.strip_suffix("u16") {
                    let (u, _) = parse_u16(s)?;
                    V::U16(u)
                } else if let Some(s) = contents.strip_suffix("u32") {
                    let (u, _) = parse_u32(s)?;
                    V::U32(u)
                } else if let Some(s) = contents.strip_suffix("u64") {
                    let (u, _) = parse_u64(s)?;
                    V::U64(u)
                } else if let Some(s) = contents.strip_suffix("u128") {
                    let (u, _) = parse_u128(s)?;
                    V::U128(u)
                } else {
                    let (u, _) = parse_u256(contents.strip_suffix("u256").unwrap())?;
                    V::U256(u)
                }
            }
            (Tok::At, _) => {
                let (_, contents) = self.advance_any()?;
                let address = Self::parse_address(contents)?;
                V::Address(address)
            }
            (Tok::Some_, _) => {
                self.advance(Tok::LParen)?;
                let start = self.inner.curr_end();
                let arg = self.parse_argument()?;
                let end = self.inner.curr_end();
                self.advance(Tok::RParen)?;
                V::Option(Spanned {
                    span: Span {
                        start,
                        end,
                        arg_idx: self.inner.span.arg_idx,
                    },
                    value: Some(Box::new(arg)),
                })
            }
            (Tok::None_, c) => V::Option(Spanned {
                span: Span {
                    start: self.inner.curr_end() - c.len(),
                    end: self.inner.curr_end(),
                    arg_idx: self.inner.span.arg_idx,
                },
                value: None,
            }),
            (Tok::DoubleQuote, contents) => V::String(contents.to_owned()),
            (Tok::SingleQuote, contents) => V::String(contents.to_owned()),
            (Tok::Vector, _) => {
                self.advance(Tok::LBracket)?;
                let values = self.parse_list_skip(
                    |p| p.parse_argument_outer(),
                    ArgumentToken::Comma,
                    Tok::RBracket,
                    Tok::Whitespace,
                    /* allow_trailing_delim */ true,
                )?;
                self.advance(Tok::RBracket)?;
                V::Vector(values)
            }
            (Tok::LBracket, _) => {
                let values = self.parse_list_skip(
                    |p| p.parse_argument_outer(),
                    ArgumentToken::Comma,
                    Tok::RBracket,
                    Tok::Whitespace,
                    /* allow_trailing_delim */ true,
                )?;
                self.advance(Tok::RBracket)?;
                V::Array(values)
            }
            (Tok::Ident, contents) if matches!(self.peek_tok(), Some(Tok::Dot)) => {
                let ident_start = self.inner.curr_end() - contents.len();
                let prefix = Identifier::new(contents)?;
                let mut fields = vec![];
                self.advance(Tok::Dot)?;
                let mut start = self.inner.curr_end();
                while let Ok((_, contents)) = self.advance_any() {
                    let end = self.inner.curr_end();
                    fields.push(Spanned {
                        span: Span {
                            start,
                            end,
                            arg_idx: self.inner.span.arg_idx,
                        },
                        value: u16::from_str(contents)
                            .context("Invalid field access -- expected a number")?,
                    });
                    if !matches!(self.peek_tok(), Some(Tok::Dot)) {
                        break;
                    }
                    self.advance(Tok::Dot)?;
                    start = self.inner.curr_end();
                }
                V::VariableAccess(
                    Spanned {
                        span: Span {
                            start: ident_start,
                            end: ident_start + contents.len(),
                            arg_idx: self.inner.span.arg_idx,
                        },
                        value: prefix,
                    },
                    fields,
                )
            }
            (Tok::Ident, contents) => V::Identifier(Identifier::new(contents)?),
            (Tok::TypeArgString, contents) => {
                let type_tokens: Vec<_> = TypeToken::tokenize(contents)?
                    .into_iter()
                    .filter(|(tok, _)| !tok.is_whitespace())
                    .collect();
                let mut parser = Parser::new(type_tokens);
                parser.advance(TypeToken::Lt)?;
                let res =
                    parser.parse_list(|p| p.parse_type(), TypeToken::Comma, TypeToken::Gt, true)?;
                parser.advance(TypeToken::Gt)?;
                if let Ok((_, contents)) = parser.advance_any() {
                    bail!("Expected end of token stream. Got: {}", contents)
                }
                V::TyArgs(res)
            }
            (Tok::Gas, _) => V::Gas,
            x => bail!("unexpected token {:?}, expected argument", x),
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::ptb::ptb_parser::parser::PTBParser;

    #[test]
    fn parse_value() {
        let values = vec![
            "true",
            "false",
            "1",
            "1u8",
            "1u16",
            "1u32",
            "1u64",
            "some(ident)",
            "some(123)",
            "some(@0x0)",
            "none",
        ];
        for s in &values {
            assert!(dbg!(PTBParser::parse_values(s)).is_ok());
        }
    }

    #[test]
    fn parse_values() {
        let values = vec![
            "true @0x0 false 1 1u8",
            "true @0x0 false 1 1u8 vector_ident another ident",
            "true @0x0 false 1 1u8 some_ident another ident some(123) none",
            "true @0x0 false 1 1u8 some_ident another ident some(123) none vector[] [] [vector[]] [vector[1]] [vector[1,2]] [vector[1,2,]]",
        ];
        for s in &values {
            assert!(dbg!(PTBParser::parse_values(s)).is_ok());
        }
    }

    #[test]
    fn parse_address() {
        let values = vec!["@0x0", "@1234"];
        for s in &values {
            assert!(dbg!(PTBParser::parse_values(s)).is_ok());
        }
    }

    #[test]
    fn parse_string() {
        let values = vec!["\"hello world\"", "'hello world'"];
        for s in &values {
            assert!(dbg!(PTBParser::parse_values(s)).is_ok());
        }
    }

    #[test]
    fn parse_vector() {
        let values = vec!["vector[]", "vector[1]", "vector[1,2]", "vector[1,2,]"];
        for s in &values {
            assert!(dbg!(PTBParser::parse_values(s)).is_ok());
        }
    }

    #[test]
    fn parse_vector_with_spaces() {
        let values = vec!["vector[ ]", "vector[1 ]", "vector[1, 2]", "vector[1, 2, ]"];
        for s in &values {
            assert!(dbg!(PTBParser::parse_values(s)).is_ok());
        }
    }

    #[test]
    fn parse_array() {
        let values = vec!["[]", "[1]", "[1,2]", "[1,2,]"];
        for s in &values {
            assert!(dbg!(PTBParser::parse_values(s)).is_ok());
        }
    }

    #[test]
    fn parse_array_with_spaces() {
        let values = vec!["[ ]", "[1 ]", "[1, 2]", "[1, 2, ]"];
        for s in &values {
            assert!(dbg!(PTBParser::parse_values(s)).is_ok());
        }
    }

    #[test]
    fn module_access() {
        let values = vec!["123::b::c", "0x0::b::c"];
        for s in &values {
            assert!(dbg!(PTBParser::parse_values(s)).is_ok());
        }
    }

    #[test]
    fn type_args() {
        let values = vec!["<u64>", "<0x0::b::c>", "<0x0::b::c, 1234::g::f>"];
        for s in &values {
            assert!(dbg!(PTBParser::parse_values(s)).is_ok());
        }
    }

    #[test]
    fn move_call() {
        let values = vec![
            "0x0::M::f",
            "<u64, 123::a::f<456::b::c>>",
            "1 2u32 vector[]",
        ];
        for s in &values {
            assert!(dbg!(PTBParser::parse_values(s)).is_ok());
        }
    }

    #[test]
    fn dotted_accesses() {
        let values = vec!["a.0", "a.1.2", "a.0.1.2"];
        for s in &values {
            assert!(dbg!(PTBParser::parse_values(s)).is_ok());
        }
    }

    #[test]
    fn dotted_accesses_invalid() {
        let values = vec!["a.b.c", "a.b.c.d", "a.b.c.d.e", "a.1,2"];
        for s in &values {
            assert!(dbg!(PTBParser::parse_values(s)).is_err());
        }
    }
}
