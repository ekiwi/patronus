// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

/// IR Nodes are only valid with their context
trait Context {
    fn add();
    fn get_width(reference: WidthRef) -> u64;
    fn get_string(reference: StringRef) -> &str;
}

struct StringRef(u16);
struct WidthRef(u16);


enum BVExpr {
    Symbol(StringRef, WidthRef)
}

impl BVExpr {
    fn width(self) -> usize {
        0 // TODO
    }
}

