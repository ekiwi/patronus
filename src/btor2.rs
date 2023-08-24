// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
use pest::Parser;

#[derive(pest_derive::Parser)]
#[grammar = "btor2.pest"]
struct Btor2Parser;

pub fn parse(input: &str) {
    Btor2Parser::parse(Rule::btor2File, input).unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_bitvec_sort() {
        Btor2Parser::parse(Rule::declBvSort, "sort bitvec 8").unwrap();
    }
}
