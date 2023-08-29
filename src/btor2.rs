// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::ir::*;
use smallvec::SmallVec;

pub fn parse(ctx: &mut Context, input: impl std::io::BufRead) -> Option<TransitionSystem> {
    match parse_private(ctx, input) {
        Ok(sys) => sys,
        Err(errors) => {
            report_errors(errors);
            None
        }
    }
}

fn parse_private(
    ctx: &mut Context,
    input: impl std::io::BufRead,
) -> std::result::Result<Option<TransitionSystem>, Errors> {
    let mut sys: Option<TransitionSystem> = None;
    let mut errors = Errors::new();
    let mut offset: usize = 0;
    for line_res in input.lines() {
        let line = line_res.expect("failed to read line");
        parse_line(ctx, &mut sys, &mut errors, &line, offset);
        offset += line.len();
    }
    if errors.is_empty() {
        Ok(sys)
    } else {
        Err(errors)
    }
}

const UNARY_OPS: [&str; 7] = ["not", "inc", "dec", "neg", "redand", "redor", "redxor"];
const BINARY_OPS: [&str; 38] = [
    "iff", "implies", "sgt", "ugt", "sgte", "ugte", "slt", "ult", "slte", "ulte", "and", "nand",
    "nor", "or", "xnor", "xor", "rol", "ror", "sll", "sra", "srl", "add", "mul", "sdiv", "udiv",
    "smod", "srem", "urem", "sub", "saddo", "uaddo", "sdivo", "udivo", "smulo", "umulo", "ssubo",
    "usubo", "concat",
];

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
    start: usize,
    end: usize,
}

type Errors = Vec<ParserError>;

fn report_errors(errors: Errors) {
    panic!(
        "TODO: report details on {} errors encountered while parsing!",
        errors.len()
    )
}

fn add_error(errors: &mut Errors, offset: usize, line: &str, token: &str, msg: String) {
    let start = (token.as_ptr() as usize) - (line.as_ptr() as usize);
    let end = start + token.len();
    let e = ParserError {
        msg,
        start: start + offset,
        end: end + offset,
    };
    errors.push(e);
}

fn to_id(token: &str) -> Option<u32> {
    token.parse::<u32>().ok()
}

fn parse_line(
    ctx: &mut Context,
    sys: &mut Option<TransitionSystem>,
    errors: &mut Errors,
    line: &str,
    offset: usize,
) {
    let cont = tokenize_line(line);
    println!("LALALALALALALAL {:?} from {:?}", cont, line);

    // TODO: deal with comments
    if cont.tokens.is_empty() {
        // early exit if there are no tokens on this line
        return;
    }

    // the first token should be an ID
    let line_id = match to_id(cont.tokens[0]) {
        None => {
            add_error(
                errors,
                offset,
                line,
                cont.tokens[0],
                "Expected valid non-negative integer ID.".to_owned(),
            );
            return; // give up
        }
        Some(id) => id,
    };

    // make sure that there is a second token following the id
    let op: &str = match cont.tokens.get(1) {
        None => {
            add_error(
                errors,
                offset,
                line,
                cont.tokens[0],
                "No operation after ID.".to_owned(),
            );
            return; // give up
        }
        Some(op) => op,
    };

    //
}

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

    #[test]
    fn parse_failures() {
        let mut ctx = Context::default();
        parse_private(&mut ctx, "".as_bytes()).expect("parsing an empty line should be fine");
        parse_private(&mut ctx, "   ".as_bytes())
            .expect("parsing an line with just whitespace should be fine");
        parse_private(&mut ctx, "  ; test bla  ".as_bytes())
            .expect("parsing an line with a comment should be fine");
        parse_private(&mut ctx, "not_an_id".as_bytes()).expect_err("invalid id");
        parse_private(&mut ctx, "-1".as_bytes()).expect_err("invalid id");
        parse_private(&mut ctx, "0".as_bytes()).expect_err("missing op");
        parse_private(&mut ctx, "0 ".as_bytes()).expect_err("missing op");
    }
}
