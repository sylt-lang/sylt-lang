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

  CheckExpected {
    msg: &'static str,
    span: Span,
    a: String,
  },

  CheckUnify {
    msg: &'static str,
    a: String,
    b: String,
    span: Span,
  },
}

impl Error {
  fn render_context(at: &Span, source: &str) -> String {
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
        span_start = Some((line_nr, line_start, i - line_start));
      }
      if i == at.1 {
        span_end = Some((line_nr, line_start, i - line_start));
        break;
      }
    }

    match (span_start, span_end) {
      (Some((start_line, start_at, start_offset)), Some((end_line, _end_at, end_offset)))
        if start_line == end_line =>
      {
        format!(
          "{:>3} | {}\n       {}{}",
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
      (Some((start_line, start_at, _)), Some((end_line, end_at, _))) if start_line != end_line => {
        source
          .chars()
          .enumerate()
          .skip(start_at)
          .take_while(|(i, c)| !(*i >= end_at - 1 && *c == '\n'))
          .map(|(_, c)| c)
          .collect::<String>()
          .split('\n')
          .enumerate()
          .map(|(offset, line)| format!("{:>3} || {}\n", start_line + offset, line))
          .collect::<String>()
      }
      (_, _) => {
        unreachable!("Passed in the wrong string, didn't find the spans that should exist, please fix the compiler")
      }
    }
  }

  fn maybe_render_context(at: &Span, source: Option<&str>) -> String {
    source
      .map(|s| Self::render_context(at, s))
      .unwrap_or("".to_string())
  }

  pub fn render(&self, source: Option<&str>) -> String {
    match self {
      Error::SynMsg { msg, token: Some(t), span } => format!(
        "> {}. Got {} instead.\n{}",
        msg,
        t,
        Self::maybe_render_context(span, source)
      ),
      Error::SynMsg { msg, token: None, span } => {
        format!("{}.\n{}", msg, Self::maybe_render_context(span, source))
      }
      Error::SynEoF { span } => format!(
        "> I reached the end of the file unexpectedly.\n{}",
        Self::maybe_render_context(span, source)
      ),
      Error::ResUnknown { name, span } => format!(
        "> I couldn't figure out what {:?} refernces. Did you make a typo?\n{}",
        name,
        Self::maybe_render_context(span, source)
      ),
      Error::ResMultiple { name, original, new } => {
        format!(
          "> I found multiple definitons of {:?}.\n first here:\n{}\n second here:\n{}\n",
          name,
          Self::maybe_render_context(original, source),
          Self::maybe_render_context(new, source)
        )
      }
      Error::CheckMsg { msg, a_span, b_span } => format!(
        "> {}\n here:\n{}\n and here:\n{}\n",
        msg,
        Self::maybe_render_context(a_span, source),
        Self::maybe_render_context(b_span, source)
      ),
      Error::CheckExpected { msg, a, span } => format!(
        "> {}. Got {} instead.\n{}\n",
        msg,
        a,
        Self::maybe_render_context(span, source)
      ),
      Error::CheckUnify { msg, a, b, span } => format!(
        "> {}.\n\n{}\n----\n{}\n\n{}",
        msg,
        a,
        b,
        Self::maybe_render_context(span, source)
      ),
    }
  }
}
