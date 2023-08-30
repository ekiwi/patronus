// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::ir::*;
use fuzzy_matcher::FuzzyMatcher;
use smallvec::SmallVec;
use std::collections::HashMap;

pub fn parse_str(ctx: &mut Context, input: &str) -> Option<TransitionSystem> {
    match Parser::new(ctx).parse(input.as_bytes()) {
        Ok(sys) => Some(sys),
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
        Ok(sys) => Some(sys),
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
    sys: TransitionSystem,
    errors: Errors,
    /// offset of the current line inside the file
    offset: usize,
    /// maps file id to type
    type_map: HashMap<LineId, Type>,
    /// maps file id to state in the Transition System
    state_map: HashMap<LineId, StateRef>,
    /// maps file id to signal in the Transition System
    signal_map: HashMap<LineId, SignalRef>,
}

type LineId = u32;

impl<'a> Parser<'a> {
    fn new(ctx: &'a mut Context) -> Self {
        let empty_str = ctx.add("");
        Parser {
            ctx,
            sys: TransitionSystem::new(empty_str),
            errors: Errors::new(),
            offset: 0,
            type_map: HashMap::new(),
            state_map: HashMap::new(),
            signal_map: HashMap::new(),
        }
    }

    fn parse(&mut self, input: impl std::io::BufRead) -> Result<TransitionSystem, Errors> {
        for line_res in input.lines() {
            let line = line_res.expect("failed to read line");
            let _ignore_errors = self.parse_line(&line);
            self.offset += line.len() + 1; // TODO: this assumes that the line terminates with a single character
        }
        if self.errors.is_empty() {
            Ok(std::mem::replace(
                &mut self.sys,
                TransitionSystem::new(self.ctx.add("")),
            ))
        } else {
            Err(std::mem::take(&mut self.errors))
        }
    }

    fn parse_line(&mut self, line: &str) -> ParseLineResult {
        let cont = tokenize_line(line);
        let tokens = &cont.tokens;
        // TODO: deal with comments
        if tokens.is_empty() {
            // early exit if there are no tokens on this line
            return Ok(());
        }

        // the first token should be an ID
        let line_id = self.parse_line_id(line, tokens[0])?;

        // make sure that there is a second token following the id
        let op: &str = match tokens.get(1) {
            None => {
                return self.add_error(line, tokens[0], "No operation after ID.".to_owned());
            }
            Some(op) => op,
        };

        // check op
        if UNARY_OPS_SET.contains(op) {
            self.require_at_least_n_tokens(line, tokens, 4)?;
            todo!("handle unary op")
        }
        if BINARY_OPS_SET.contains(op) {
            self.require_at_least_n_tokens(line, tokens, 5)?;
            todo!("handle binary op")
        }
        self.require_at_least_n_tokens(line, tokens, 3)?;
        let expr: Option<ExprRef> = match op {
            "sort" => {
                self.parse_sort(line, tokens, line_id)?;
                None
            }
            "const" | "constd" | "consth" | "zero" | "one" => {
                Some(self.parse_format(line, tokens, op)?)
            }
            "state" => {
                self.parse_state(line, &cont, line_id)?;
                None
            }
            "init" => {
                self.parse_state_init(line, &cont)?;
                None
            }
            other => {
                if OTHER_OPS_SET.contains(other) {
                    panic!("TODO: implement support for {other} operation")
                } else {
                    return self.invalid_op_error(line, op);
                }
            }
        };
        if let Some(e) = expr {
            self.add_signal(line_id, e)?;
        }
        Ok(())
    }

    fn check_expr_type(
        &mut self,
        actual: ExprRef,
        expected: &Type,
        line: &str,
        token: &str,
        msg: &str,
    ) -> ParseLineResult {
        let actual_tpe = match actual.type_check(self.ctx) {
            Ok(tpe) => tpe,
            Err(e) => {
                return self.add_error(line, token, e.get_msg().to_string());
            }
        };
        self.check_type(&actual_tpe, expected, line, token, msg)
    }

    fn check_type(
        &mut self,
        actual: &Type,
        expected: &Type,
        line: &str,
        token: &str,
        msg: &str,
    ) -> ParseLineResult {
        if actual == expected {
            Ok(())
        } else {
            self.add_error(line, token, format!("{msg}: {actual} != {expected}"))
        }
    }

    fn add_signal(&mut self, line_id: LineId, expr: ExprRef) -> ParseLineResult {
        let signal_ref = self.sys.add_signal(expr, SignalKind::Node);
        self.signal_map.insert(line_id, signal_ref);
        Ok(())
    }

    fn get_label_name(&mut self, cont: &LineTokens, default: &str) -> StringRef {
        let base_str: &str = cont.tokens.get(3).unwrap_or(&default);
        // TODO: look into comment for better names
        self.ctx.add_unique_str(base_str)
    }

    fn parse_state(&mut self, line: &str, cont: &LineTokens, line_id: LineId) -> ParseLineResult {
        let tpe = self.get_tpe_from_id(line, cont.tokens[2])?;
        let name = self.get_label_name(cont, "state");
        let sym = Expr::symbol(name, tpe);
        let sym_ref = self.ctx.add(sym);
        let state_ref = self.sys.add_state(self.ctx, sym_ref);
        self.state_map.insert(line_id, state_ref);
        Ok(())
    }

    fn parse_state_init(&mut self, line: &str, cont: &LineTokens) -> ParseLineResult {
        self.require_at_least_n_tokens(line, &cont.tokens, 5)?;
        let tpe = self.get_tpe_from_id(line, cont.tokens[2])?;
        let state_ref = self.get_state_from_id(line, cont.tokens[3])?;
        let state_sym = self.sys.get(state_ref).symbol;
        let state_tpe = state_sym.type_check(self.ctx).unwrap();
        let state_name = state_sym.get_symbol_name(self.ctx).unwrap().to_string();
        let expr = self.get_expr_from_signal_id(line, cont.tokens[4])?;
        self.check_expr_type(
            expr,
            &tpe,
            line,
            cont.tokens[4],
            &format!("[{state_name}.init] Expressions has mismatched type"),
        )?;
        self.check_type(
            &state_tpe,
            &tpe,
            line,
            cont.tokens[4],
            &format!("[{state_name}.init] Expression type does not match state type."),
        )?;
        todo!("actually add init to state");
        Ok(())
    }

    fn parse_line_id(&mut self, line: &str, token: &str) -> ParseLineResult<LineId> {
        match token.parse::<LineId>().ok() {
            None => {
                let _ = self.add_error(
                    line,
                    token,
                    "Expected valid non-negative integer ID.".to_owned(),
                );
                Err(())
            }
            Some(id) => Ok(id),
        }
    }

    fn parse_format(&mut self, line: &str, tokens: &[&str], op: &str) -> ParseLineResult<ExprRef> {
        // derive width from type
        let width = self.get_bv_width(line, tokens[2])?;

        match op {
            "zero" => Ok(self.ctx.zero(width)),
            "one" => Ok(self.ctx.one(width)),
            "const" => self.parse_bv_lit_str(line, tokens[3], 2, width),
            "constd" => self.parse_bv_lit_str(line, tokens[3], 10, width),
            "consth" => self.parse_bv_lit_str(line, tokens[3], 16, width),
            other => panic!("Did not expect {other} as a possible format op!"),
        }
    }

    fn parse_bv_lit_str(
        &mut self,
        line: &str,
        token: &str,
        base: u32,
        width: WidthInt,
    ) -> ParseLineResult<ExprRef> {
        match BVLiteralInt::from_str_radix(token, base) {
            Ok(val) => {
                if bv_value_fits_width(val, width) {
                    Ok(self.ctx.bv_lit(val, width))
                } else {
                    let _ = self.add_error(
                        line,
                        token,
                        format!("Value {val} does not fit into a bit-vector of width {width}"),
                    );
                    Err(())
                }
            }
            Err(_) => {
                let _ = self.add_error(
                    line,
                    token,
                    format!("Failed to parse as an integer of base {base}"),
                );
                Err(())
            }
        }
    }

    fn get_bv_width(&mut self, line: &str, token: &str) -> ParseLineResult<WidthInt> {
        let tpe = self.get_tpe_from_id(line, token)?;
        match tpe {
            Type::BV(width) => Ok(width),
            Type::Array(tpe) => {
                let _ = self.add_error(
                    line,
                    token,
                    format!(
                        "Points to an array type `{tpe:?}`, but a bit-vector type is required!"
                    ),
                );
                Err(())
            }
        }
    }

    fn get_tpe_from_id(&mut self, line: &str, token: &str) -> ParseLineResult<Type> {
        let tpe_id = self.parse_line_id(line, token)?;
        match self.type_map.get(&tpe_id) {
            None => {
                let _ = self.add_error(
                    line,
                    token,
                    format!("ID `{tpe_id}` does not point to a valid type!"),
                );
                Err(())
            }
            Some(tpe) => Ok(tpe.clone()),
        }
    }

    fn get_state_from_id(&mut self, line: &str, token: &str) -> ParseLineResult<StateRef> {
        let state_id = self.parse_line_id(line, token)?;
        match self.state_map.get(&state_id) {
            None => {
                let _ = self.add_error(
                    line,
                    token,
                    format!("ID `{state_id}` does not point to a valid state!"),
                );
                Err(())
            }
            Some(state) => Ok(*state),
        }
    }

    fn get_expr_from_signal_id(&mut self, line: &str, token: &str) -> ParseLineResult<ExprRef> {
        let signal = self.get_signal_from_id(line, token)?;
        Ok(self.sys.get(signal).expr)
    }

    fn get_signal_from_id(&mut self, line: &str, token: &str) -> ParseLineResult<SignalRef> {
        let signal_id = self.parse_line_id(line, token)?;
        match self.signal_map.get(&signal_id) {
            None => {
                let _ = self.add_error(
                    line,
                    token,
                    format!("ID `{signal_id}` does not point to a valid signal!"),
                );
                Err(())
            }
            Some(signal) => Ok(*signal),
        }
    }

    fn parse_sort(&mut self, line: &str, tokens: &[&str], line_id: LineId) -> ParseLineResult {
        self.require_at_least_n_tokens(line, tokens, 3)?;
        match tokens[2] {
            "bitvec" => {
                self.require_at_least_n_tokens(line, tokens, 4)?;
                let width = self.parse_width_int(line, tokens[3], "bit-vector width")?;
                self.type_map.insert(line_id, Type::BV(width));
                Ok(())
            }
            "array" => {
                self.require_at_least_n_tokens(line, tokens, 5)?;
                let index_width = self.parse_width_int(line, tokens[3], "array index width")?;
                let data_width = self.parse_width_int(line, tokens[4], "array data width")?;
                self.type_map.insert(
                    line_id,
                    Type::Array(ArrayType {
                        index_width,
                        data_width,
                    }),
                );
                Ok(())
            }
            other => {
                self.add_error(
                    line,
                    tokens[2],
                    format!("Expected `bitvec` or `array`. Not `{other}`."),
                )
            }
        }
    }

    fn parse_width_int(
        &mut self,
        line: &str,
        token: &str,
        kind: &str,
    ) -> ParseLineResult<WidthInt> {
        match token.parse::<WidthInt>() {
            Ok(width) => Ok(width),
            Err(_) => {
                let _ = self.add_error(
                    line,
                    token,
                    format!(
                        "Not a valid {kind}. An integer between {} and {} is required!",
                        WidthInt::MAX,
                        WidthInt::MIN
                    ),
                );
                Err(())
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
        tokens: &[&str],
        n: usize,
    ) -> ParseLineResult {
        if tokens.len() < n {
            let op = tokens[1];
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
    codespan_reporting::term::emit(&mut writer.lock(), &config, file, &diagnostic).unwrap();
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
type ParseLineResult<T = ()> = std::result::Result<T, ()>;

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

    fn parse_private(code: &str) -> Result<TransitionSystem, Errors> {
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
