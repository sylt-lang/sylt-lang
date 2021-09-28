require 'rouge'

class Sylt < ::Rouge::RegexLexer
  title 'Sylt'
  tag 'sylt'
  filenames '*.sy'

  state :root do
    # Whitespace stuff
    rule %r(\n), Text
    rule %r([^\S\n]), Text

    rule %r(//.*?$), Comment::Single

    rule %r(fn|do|end), Keyword

    rule %r([A-Za-z_][A-Za-z0-9_]*), Name

    rule %r("), Str::Double, :string

    rule %r([\(\)]), Punctuation

    rule %r(::), Operator
  end

  state :string do
    rule %r("), Str::Double, :pop!
    rule %r([^"]+), Str::Double
  end

  state :comment do
    rule %r($), Text, :pop!
    rule %r([^$]), Comment::Single
  end
end
