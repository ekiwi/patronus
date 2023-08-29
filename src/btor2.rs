// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::ir::*;
use codespan_reporting::term;
use fuzzy_matcher::FuzzyMatcher;
use smallvec::SmallVec;

pub fn parse_str(ctx: &mut Context, input: &str) -> Option<TransitionSystem> {
    match Parser::new(ctx).parse(input.as_bytes()) {
        Ok(sys) => sys,
        Err(errors) => {
            report_errors(errors, "str", input);
            None
        }
    }
}

pub fn parse_file(ctx: &mut Context, path: &std::path::Path) -> Option<TransitionSystem> {
    let f = std::fs::File::open(path).expect("Failed to open btor file!");
    let reader = std::io::BufReader::new(f);
    match Parser::new(ctx).parse(reader) {
        Ok(sys) => sys,
        Err(errors) => {
            report_errors(
                errors,
                path.file_name().unwrap().to_str().unwrap(),
                &std::fs::read_to_string(path).unwrap(),
            );
            None
        }
    }
}

struct Parser<'a> {
    ctx: &'a mut Context,
    sys: Option<TransitionSystem>,
    errors: Errors,
    offset: usize,
}

impl<'a> Parser<'a> {
    fn new(ctx: &'a mut Context) -> Self {
        Parser {
            ctx,
            sys: None,
            errors: Errors::new(),
            offset: 0,
        }
    }

    fn parse(&mut self, input: impl std::io::BufRead) -> Result<Option<TransitionSystem>, Errors> {
        for line_res in input.lines() {
            let line = line_res.expect("failed to read line");
            let _ignore_errors = self.parse_line(&line);
            self.offset += line.len() + 1; // TODO: this assumes that the line terminates with a single character
        }
        if self.errors.is_empty() {
            Ok(std::mem::replace(&mut self.sys, None))
        } else {
            Err(std::mem::replace(&mut self.errors, Errors::new()))
        }
    }

    fn parse_line(&mut self, line: &str) -> ParseLineResult {
        let cont = tokenize_line(line);
        let tokens = cont.tokens;
        // TODO: deal with comments
        if tokens.is_empty() {
            // early exit if there are no tokens on this line
            return Ok(());
        }

        // the first token should be an ID
        let line_id = match to_id(tokens[0]) {
            None => {
                return self.add_error(
                    line,
                    tokens[0],
                    "Expected valid non-negative integer ID.".to_owned(),
                );
            }
            Some(id) => id,
        };

        // make sure that there is a second token following the id
        let op: &str = match tokens.get(1) {
            None => {
                return self.add_error(line, tokens[0], "No operation after ID.".to_owned());
            }
            Some(op) => op,
        };

        // check op
        if UNARY_OPS_SET.contains(op) {
            self.require_at_least_n_tokens(line, op, &tokens, 4)?;
            todo!("handle unary op")
        }
        if BINARY_OPS_SET.contains(op) {
            self.require_at_least_n_tokens(line, op, &tokens, 5)?;
            todo!("handle binary op")
        }
        match op {
            "sort" => {
                self.require_at_least_n_tokens(line, op, &tokens, 3)?;
                match tokens[2] {
                    "bitvec" => todo!("bitvec sort"),
                    "array" => todo!("array sort"),
                    other => {
                        return self.add_error(
                            line,
                            tokens[2],
                            format!("Expected `bitvec` or `array`. Not `{other}`."),
                        )
                    }
                }
            }
            other => {
                if OTHER_OPS_SET.contains(other) {
                    panic!("TODO: implement support for {other} operation")
                } else {
                    return self.invalid_op_error(line, op);
                }
            }
        }
    }

    fn add_error(&mut self, line: &str, token: &str, msg: String) -> ParseLineResult {
        let explain = "".to_owned(); // TODO: how do we best utilize both msg and explain?
        let start = str_offset(token, line);
        let end = start + token.len();
        let e = ParserError {
            msg,
            explain,
            start: start + self.offset,
            end: end + self.offset,
        };
        self.errors.push(e);
        Err(())
    }

    fn require_at_least_n_tokens(
        &mut self,
        line: &str,
        op: &str,
        tokens: &[&str],
        n: usize,
    ) -> ParseLineResult {
        if tokens.len() < n {
            let start = str_offset(op, line);
            let last_token = tokens.last().unwrap();
            let end = str_offset(last_token, line) + last_token.len();
            self.add_error(
                line,
                &line[start..end],
                format!(
                    "{op} requires at least {n} tokens, only {} provided",
                    tokens.len()
                ),
            )
        } else {
            Ok(())
        }
    }

    fn invalid_op_error(&mut self, line: &str, op: &str) -> ParseLineResult {
        let all_ops = UNARY_OPS
            .iter()
            .chain(BINARY_OPS.iter())
            .chain(OTHER_OPS.iter());
        let matcher = fuzzy_matcher::skim::SkimMatcherV2::default();
        let mut matches: Vec<(&&str, i64)> = all_ops
            .flat_map(|other| matcher.fuzzy_match(other, op).map(|s| (other, s)))
            .collect();
        matches.sort_by_key(|(_, s)| -(*s));
        let n_matches = std::cmp::min(matches.len(), 5);
        let suggestions = matches
            .iter()
            .take(n_matches)
            .map(|(n, _)| **n)
            .collect::<Vec<&str>>()
            .join(", ");
        self.add_error(
            line,
            op,
            format!("Invalid op {op}. Did you mean: {suggestions}?"),
        )
    }
}

// Line Tokenizer
#[derive(Default, Debug)]
struct LineTokens<'a> {
    tokens: SmallVec<[&'a str; 4]>,
    comment: Option<&'a str>,
}

const NO_TOKEN: usize = usize::MAX;
fn tokenize_line(line: &str) -> LineTokens {
    if line.is_empty() {
        // special handling for empty lines
        return LineTokens::default();
    }
    let line_len = line.len();
    let mut out = LineTokens::default();
    let mut token_start: usize = NO_TOKEN;
    #[inline]
    fn finish_token<'a>(
        token_start: &mut usize,
        out: &mut LineTokens<'a>,
        line: &'a str,
        ii: usize,
    ) {
        if *token_start != NO_TOKEN {
            out.tokens.push(&line[*token_start..ii]);
            *token_start = NO_TOKEN;
        }
    }

    for (ii, cc) in line.char_indices() {
        match cc {
            // white space character
            ' ' | '\t' => finish_token(&mut token_start, &mut out, line, ii),
            // comment start
            ';' => {
                finish_token(&mut token_start, &mut out, line, ii);
                out.comment = Some(&line[ii + 1..line_len]);
                return out;
            }
            _ => {
                if token_start == NO_TOKEN {
                    token_start = ii
                }
            }
        }
    }
    finish_token(&mut token_start, &mut out, line, line_len);
    out
}

#[derive(Debug)]
struct ParserError {
    msg: String,
    explain: String, // displayed next to offending token
    start: usize,
    end: usize,
}

type Errors = Vec<ParserError>;

fn report_errors(errors: Errors, name: &str, source: &str) {
    let report_file = codespan_reporting::files::SimpleFile::new(name, source);
    for err in errors.into_iter() {
        report_error(err, &report_file);
    }
}

fn report_error<'a>(error: ParserError, file: &codespan_reporting::files::SimpleFile<&str, &str>) {
    let diagnostic = codespan_reporting::diagnostic::Diagnostic::error()
        .with_message(error.msg)
        .with_labels(vec![codespan_reporting::diagnostic::Label::primary(
            (),
            error.start..error.end,
        )
        .with_message(error.explain)]);
    let writer = codespan_reporting::term::termcolor::StandardStream::stderr(
        codespan_reporting::term::termcolor::ColorChoice::Auto,
    );
    let config = codespan_reporting::term::Config::default();
    term::emit(&mut writer.lock(), &config, file, &diagnostic).unwrap();
}

fn str_offset(needle: &str, haystack: &str) -> usize {
    let offset = (needle.as_ptr() as usize) - (haystack.as_ptr() as usize);
    assert!(
        offset < haystack.len(),
        "{} is not fully contained in {}",
        needle,
        haystack
    );
    offset
}

fn to_id(token: &str) -> Option<u32> {
    token.parse::<u32>().ok()
}

const UNARY_OPS: [&str; 7] = ["not", "inc", "dec", "neg", "redand", "redor", "redxor"];
const BINARY_OPS: [&str; 40] = [
    "iff", "implies", "sgt", "ugt", "sgte", "ugte", "slt", "ult", "slte", "ulte", "and", "nand",
    "nor", "or", "xnor", "xor", "rol", "ror", "sll", "sra", "srl", "add", "mul", "sdiv", "udiv",
    "smod", "srem", "urem", "sub", "saddo", "uaddo", "sdivo", "udivo", "smulo", "umulo", "ssubo",
    "usubo", "concat", "eq", "neq",
];
const OTHER_OPS: [&str; 19] = [
    "sort",
    "input",
    "output",
    "bad",
    "constraint",
    "fair",
    "state",
    "next",
    "init",
    "const",
    "constd",
    "consth",
    "zero",
    "one",
    "ones",
    "slice",
    "read",
    "write",
    "ite",
];

lazy_static! {
    static ref UNARY_OPS_SET: std::collections::HashSet<&'static str> =
        std::collections::HashSet::from(UNARY_OPS);
    static ref BINARY_OPS_SET: std::collections::HashSet<&'static str> =
        std::collections::HashSet::from(BINARY_OPS);
    static ref OTHER_OPS_SET: std::collections::HashSet<&'static str> =
        std::collections::HashSet::from(OTHER_OPS);
}

/// Indicated success or failure. Errors and data is not returned, but rather added to the context.
type ParseLineResult = std::result::Result<(), ()>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tokenize() {
        // correct number of tokens
        assert_eq!(tokenize_line("").tokens.len(), 0);
        assert_eq!(tokenize_line("a").tokens.len(), 1);
        assert_eq!(tokenize_line(" a").tokens.len(), 1);
        assert_eq!(tokenize_line("a ").tokens.len(), 1);
        assert_eq!(tokenize_line(" a ").tokens.len(), 1);
        assert_eq!(tokenize_line("a b").tokens.len(), 2);
        assert_eq!(tokenize_line("a \t b").tokens.len(), 2);
        assert_eq!(tokenize_line("a     b").tokens.len(), 2);
        assert_eq!(tokenize_line("a b ; c").tokens.len(), 2);
        assert_eq!(tokenize_line("a b;c").tokens.len(), 2);
        // correctly deal with whitespace
        assert_eq!(tokenize_line("a").tokens[0], "a");
        assert_eq!(tokenize_line(" a").tokens[0], "a");
        assert_eq!(tokenize_line("a ").tokens[0], "a");
        assert_eq!(tokenize_line(" a ").tokens[0], "a");
        // comments
        let comment_res = tokenize_line("a b; c");
        assert_eq!(comment_res.comment, Some(" c"));
        assert_eq!(comment_res.tokens[0], "a");
        assert_eq!(comment_res.tokens[1], "b");
        // unicode (not sure if this is actually supported by the btor2 format...)
        let unicode_res = tokenize_line("✔ 1✖2  ○;○123");
        assert_eq!(unicode_res.tokens.len(), 3);
        assert!(unicode_res.comment.is_some());
        assert_eq!(unicode_res.tokens[0], "✔");
        assert_eq!(unicode_res.tokens[1], "1✖2");
        assert_eq!(unicode_res.tokens[2], "○");
        assert_eq!(unicode_res.comment.unwrap(), "○123");
    }

    fn parse_private(code: &str) -> Result<Option<TransitionSystem>, Errors> {
        let mut ctx = Context::default();
        Parser::new(&mut ctx).parse(code.as_bytes())
    }

    #[test]
    fn parse_failures() {
        parse_private("").expect("parsing an empty line should be fine");
        parse_private("   ").expect("parsing an line with just whitespace should be fine");
        parse_private("  ; test bla  ").expect("parsing an line with a comment should be fine");
        parse_private("not_an_id").expect_err("invalid id");
        parse_private("-1").expect_err("invalid id");
        parse_private("0").expect_err("missing op");
        parse_private("0 ").expect_err("missing op");
    }
}
