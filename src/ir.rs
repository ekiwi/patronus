// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

/// IR Nodes are only valid with their context
trait Context<'a> {
    fn add();
    fn get_width(reference: WidthRef) -> u64;
    fn get_string(reference: StringRef) -> &'a str;
}

struct StringRef(u16);
struct WidthRef(u16);
struct BVExprRef(u32);




enum BVExpr {
    Symbol(StringRef, WidthRef),
    // unary operations
    

    // binary operations
    Add(BVExprRef, BVExprRef)
}

impl BVExpr {
    fn width(self) -> usize {
        0 // TODO
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ir_type_size() {
        assert_eq!(std::mem::size_of::<StringRef>(), 2);
        assert_eq!(std::mem::size_of::<WidthRef>(), 2);
        // 4 bytes for the tag, 8 bytes for the largest field
        assert_eq!(std::mem::size_of::<BVExpr>(), 12);
    }
}