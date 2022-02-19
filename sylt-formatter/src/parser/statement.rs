use std::ops::Range;

use super::expression::Expression;

/// A statement in sylt
#[derive(Debug)]
pub enum Statement<'a> {
    /// A definition of a variable
    ///
    /// Ex: `var :: <expr>`
    Definition {
        /// The variable name
        var: (&'a String, &'a Range<usize>),

        /// The expression defines the variable
        expr: Expression<'a>,
    },
}
