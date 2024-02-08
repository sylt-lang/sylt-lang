use std::fmt::Display;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub struct Span(pub usize, pub usize, pub usize);

impl Span {
  pub fn merge(self, other: Self) -> Self {
    assert_eq!(self.2, other.2, "Can't join spans from different files");
    Self(self.0.min(other.0), self.1.max(other.1), self.2)
  }
}

impl Display for Span {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}-{}", self.0, self.1)
  }
}

#[derive(Clone, Debug)]
pub enum Error {
  // Special errors which are caused by unfortunate realities like files not existing.
  Special(String),

  /// FIXME: ?
  SynMsg {
    msg: &'static str,
    span: Span,
    token: Option<String>,
  },

  /// Parsing reached eof
  SynEoF {
    span: Span,
  },

  /// No definition of variable
  ResUnknown {
    ns: String,
    name: String,
    span: Span,
  },

  /// Multiple definitions for a variable
  ResMultiple {
    ns: String,
    name: String,
    original: Span,
    new: Span,
  },

  /// Missing enum constructor
  ResNoEnumConst {
    ty_name: String,
    at: Span,
    const_name: String,
  },

  /// Missing enum
  ResNoEnum {
    ty_name: String,
    at: Span,
  },

  /// FIXME: ?
  ResMsg {
    msg: String,
    span: Span,
  },

  /// FIXME: ?
  CheckMsg {
    msg: &'static str,
    a_span: Span,
    b_span: Span,
  },

  /// FIXME: ?
  CheckExpected {
    msg: &'static str,
    span: Span,
    a: String,
  },

  /// Missing requirements
  CheckReq {
    msg: &'static str,
    span: Span,
    a: String,
    req: String,
  },

  /// Unification failure
  CheckUnify {
    msg: &'static str,
    a: String,
    b: String,
    span: Span,
  },

  /// FIXME: ?
  CheckExtraLabel {
    a: String,
    b: String,
    field: String,
    span: Span,
  },

  /// An error message with an associated record field
  CheckField {
    field: String,
    inner: Box<Error>,
  },
}

impl Error {
  /// Show the line(s) of a span from the source code
  fn render_context(at: &Span, filename: &str, source: &str) -> Option<String> {
    let mut line_nr = 1;
    let mut line_start = 0;

    let mut span_start = None;
    let mut span_end = None;
    for (i, c) in source.chars().enumerate() {
      if c == '\n' {
        line_nr += 1;
        line_start = i + 1;
      }
      if i == at.0 {
        span_start = Some((line_nr, line_start, i - i.min(line_start)));
      }
      if i == at.1 {
        span_end = Some((line_nr, line_start, i - i.min(line_start)));
        break;
      }
    }

    Some(match (span_start, span_end) {
      (Some((start_line, start_at, start_offset)), Some((end_line, _end_at, end_offset)))
        if start_line == end_line =>
      {
        format!(
          "{}\n{:>3}| {}\n     {}{}",
          filename,
          start_line,
          source
            .chars()
            .skip(start_at)
            .take_while(|c| *c != '\n')
            .collect::<String>(),
          (0..start_offset).map(|_| ' ').collect::<String>(),
          (0..(end_offset - start_offset))
            .map(|_| '^')
            .collect::<String>(),
        )
      }
      (Some((start_line, start_at, start_offset)), None) => {
        let line = source
          .chars()
          .skip(start_at)
          .take_while(|c| *c != '\n')
          .collect::<String>();
        format!(
          "{}\n{:>3}| {}\n     {}{}",
          filename,
          start_line,
          line,
          (0..start_offset).map(|_| ' ').collect::<String>(),
          (0..(line.len() - start_offset))
            .map(|_| '^')
            .collect::<String>(),
        )
      }
      (Some((start_line, start_at, _)), Some((end_line, end_at, _))) if start_line != end_line => {
        format!(
          "{}\n{}",
          filename,
          source
            .chars()
            .enumerate()
            .skip(start_at)
            // Of-by-one?
            .take_while(|(i, c)| !(*i >= end_at && *c == '\n'))
            .map(|(_, c)| c)
            .collect::<String>()
            .split('\n')
            .enumerate()
            .map(|(offset, line)| format!("{:>3}| {}\n", start_line + offset, line))
            .collect::<String>()
        )
      }
      _ => {
        return None;
      }
    })
  }

  /// Try to render the context, handle reaching EOF
  fn maybe_render_context(at: &Span, source: &[Option<(String, String)>]) -> String {
    source
      .get(at.2)
      .map(|x| x.as_ref())
      .flatten()
      .map(|(n, s)| {
        Self::render_context(at, n, s).unwrap_or_else(|| format!("  No context for {}, EOF", n))
      })
      .unwrap_or("".to_string())
  }

  /// Only convert to string - you probably only want to call this if you're an LSP
  pub fn convert(&self) -> (String, Vec<Span>) {
    match self {
      Error::Special(err) => (format!("! {}.", err), Vec::new()),
      Error::SynMsg { msg, token: Some(t), span } => {
        (format!("> {}. Got {} instead.", msg, t,), vec![*span])
      }
      Error::SynMsg { msg, token: None, span } => (format!("{}", msg), vec![*span]),
      Error::SynEoF { span } => (
        format!("> I reached the end of the file unexpectedly.",),
        vec![*span],
      ),
      Error::ResUnknown { ns, name, span } => (
        format!(
          "> I couldn't figure out what '{:?} {:?}' references. Did you make a typo?",
          ns, name,
        ),
        vec![*span],
      ),
      Error::ResMultiple { ns, name, original, new } => (
        format!("> I found multiple definitons of '{:?} {:?}'.", ns, name,),
        vec![*original, *new],
      ),
      Error::ResNoEnumConst { ty_name, const_name, at } => (
        format!(
          "> The enum {:?} does not have a constructor named {:?}",
          ty_name, const_name
        ),
        vec![*at],
      ),
      Error::ResNoEnum { ty_name, at } => (
        format!("> The name {:?} is not an enum", ty_name),
        vec![*at],
      ),
      Error::ResMsg { msg, span } => (format!("> {}", msg), vec![*span]),

      Error::CheckMsg { msg, a_span, b_span } => (format!("> {}", msg,), vec![*a_span, *b_span]),
      Error::CheckExpected { msg, a, span } => {
        (format!("> {}. Got {} instead.", msg, a,), vec![*span])
      }
      Error::CheckReq { msg, a, req, span } => (
        format!("> {}.\n\n{}\nis not\n{}", msg, a, req,),
        vec![*span],
      ),
      Error::CheckUnify { msg, a, b, span } => {
        (format!("> {}.\n\n{}\n----\n{}", msg, a, b), vec![*span])
      }
      Error::CheckExtraLabel { a, b, field, span } => (
        format!(
          "> Found extra label \"{}\" while unifying records.\n\n{}\n----\n{}",
          field, a, b
        ),
        vec![*span],
      ),
      Error::CheckField { field, inner } => {
        let (msg, annot) = inner.convert();
        (
          format!("> While checking label \"{}\".\n{}", field, msg),
          annot,
        )
      }
    }
  }

  /// Add in context and convert to string
  pub fn render(&self, source: &[Option<(String, String)>]) -> String {
    let (msg, annot) = self.convert();
    [
      [msg, "".to_string()].as_slice(),
      annot
        .into_iter()
        .map(|a| Self::maybe_render_context(&a, source))
        .collect::<Vec<_>>()
        .as_slice(),
    ]
    .concat()
    .join("\n")
  }
}
