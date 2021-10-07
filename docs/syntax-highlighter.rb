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

    rule %r((and|or|not|if|else|loop|break|continue|blob|in|is|do|end|fn|ret|use|as)\b), Keyword
    rule %r((bool|float|int|str|void)\b), Keyword::Type
    rule %r((false|true|nil)\b), Keyword::Constant

    rule %r([A-Za-z_][A-Za-z0-9_]*), Name

    rule %r((?i)(\d*\.\d+|\d+\.\d*)(e[+-]?\d+)?'), Num::Float
    rule %r(\d+), Num::Integer
    rule %r("), Str::Double, :string

    rule %r([\(\)\[\]\{\},#]), Punctuation

    rule %r(\.|::|:=|:|=|->|'|\+|-|\*|\/|>|>=|<|<=|==|!=|\+=|-=|\/=|\*=|\?|\||!), Operator
  end

  state :string do
    rule %r("), Str::Double, :pop!
    rule %r([^"]+), Str::Double
  end
end
