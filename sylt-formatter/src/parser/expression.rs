use std::ops::Range;

/// An expression in sylt
#[derive(Debug)]
pub enum Expression<'a> {
    /// An integer value
    Int(i64, &'a Range<usize>),

    /// A floating point value
    Float(f64, &'a Range<usize>),
}
