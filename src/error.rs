#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Span(pub usize, pub usize);

impl Span {
  pub fn merge(self, other: Self) -> Self {
    Self(self.0.min(other.0), self.1.max(other.1))
  }
}

#[derive(Clone, Debug)]
pub enum Error {
  SynMsg {
    msg: &'static str,
    span: Span,
    token: Option<String>,
  },

  SynEoF {
    span: Span,
  },

  ResUnknown {
    name: String,
    span: Span,
  },

  ResMultiple {
    name: String,
    original: Span,
    new: Span,
  },

  CheckMsg {
    msg: &'static str,
    a_span: Span,
    b_span: Span,
  },

  CheckUnify {
    msg: &'static str,
    a: String,
    b: String,
    span: Span,
  },
}
