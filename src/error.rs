#[derive(Debug, Clone, Copy)]
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
}
