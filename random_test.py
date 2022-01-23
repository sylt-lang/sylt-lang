"""
Generate random sylt tests.

The reason why statements can have a size bigger than 1 is that sylt compiles
larger expressions to multiple assignments, and lua has a hard limit of 200
local variables, which we want to avoid.

A function is not really a statement, but it makes more sense in this
abstraction.

Future improvements:
    - Guarantee longer dependency chains by not just randomly choosing
      a function/value
"""


from random import choice, random, shuffle
from typing import Union

indented = lambda s: "\n".join(map(lambda ss: "  " + ss, s.splitlines())) + "\n"  # noqa
current_id_number = 0


# Limit amount of assignments, since sylt compiles expressions to different assignments
# Lua only supports up to 200.
BLOCK_ASSIGNMENTS = 80
# Limit nested expressions and functions
NESTED_EXPRESSION_LIMIT = 2
NESTED_FUNCTION_LIMIT = 3


def gen_id():
    global current_id_number
    current_id_number += 1
    return f"v{current_id_number}"


class Node:
    def __init__(self, parent=None):
        self.parent = parent


class Expression(Node):
    def __init__(self, parent=None):
        super().__init__(parent)

    def compose(self) -> str:
        raise NotImplementedError

    def size(self) -> int:
        raise NotImplementedError

    @staticmethod
    def generate(scope_fns, scope_vars, depth=0):
        if depth >= NESTED_EXPRESSION_LIMIT:
            return Value.generate(scope_fns, scope_vars)
        else:
            return choice(
                [
                    lambda: Value.generate(scope_fns, scope_vars),
                    lambda: Operator.generate(scope_fns, scope_vars, depth),
                ]
                + (
                    [lambda: FnCall.generate(scope_fns, scope_vars, depth)]
                    if scope_fns
                    else []
                )
            )()


class Value(Expression):
    """
    A value is a variable or a number
    """

    def __init__(self, value: Union[int, str]):
        super().__init__()

        self.value: Union[int, str] = value

    def compose(self) -> str:
        return str(self.value)

    def size(self) -> int:
        return 1

    @staticmethod
    def generate(scope_fns, scope_vars):
        if scope_vars and random() > 0.7:
            return Value(choice(scope_vars))
        else:
            return Value(int(random() * 100))


class Operator(Expression):
    def __init__(self, lhs: Expression, operator: str, rhs: Expression):
        super().__init__()

        self.lhs = lhs
        self.operator = operator
        self.rhs = rhs

    def compose(self) -> str:
        return f"({self.lhs.compose()} {self.operator} {self.rhs.compose()})"

    def size(self) -> int:
        return self.lhs.size() + 1 + self.rhs.size()

    @staticmethod
    def generate(scope_fns, scope_vars, depth):
        op = choice(["+", "-", "*"])
        lhs = Expression.generate(scope_fns, scope_vars, depth + 1)
        rhs = Expression.generate(scope_fns, scope_vars, depth + 1)
        return Operator(lhs, op, rhs)


class FnCall(Expression):
    def __init__(self, fn: str, arg: Expression):
        super().__init__()

        self.fn = fn
        self.arg = arg

    def compose(self) -> str:
        return f"{self.fn}({self.arg.compose()})"

    def size(self) -> int:
        return 1

    @staticmethod
    def generate(scope_fns, scope_vars, depth):
        return FnCall(
            choice(scope_fns), Expression.generate(scope_fns, scope_vars, depth + 1)
        )


class Statement(Node):
    def __init__(self):
        super().__init__()

        self.size = 1

    def compose(self) -> str:
        raise NotImplementedError

    @staticmethod
    def generate(scope_fns, scope_vars, depth=0):
        if depth >= NESTED_FUNCTION_LIMIT:
            return Assignment.generate(scope_fns, scope_vars)
        return choice(
            [
                lambda: Assignment.generate(scope_fns, scope_vars),
                lambda: Function.generate(scope_fns, scope_vars, depth),
            ]
        )()


class Assignment(Statement):
    def __init__(self, ident, const: bool, expr: Expression):
        super().__init__()

        self.ident = ident
        self.const = const
        self.expr = expr

        self.size += expr.size()

    def compose(self) -> str:
        return f"{self.ident} :{':' if self.const else '='} {self.expr.compose()}\n"

    @staticmethod
    def generate(scope_fns, scope_vars):
        ident = gen_id()
        const = random() > 0.5
        expr = Expression.generate(scope_fns, scope_vars)

        return Assignment(ident, const, expr)


class Block(Node):
    def __init__(self, statements: list[Statement], fns: list[str], vars: list[str]):
        super().__init__()

        self.fns = fns
        self.vars = vars

        self.statements: list[Statement] = statements

    def compose(self) -> str:
        return "do\n" + self._compose() + "end\n"

    def _compose(self) -> str:
        return "".join(f"{child.compose()}" for child in self.statements)

    @staticmethod
    def generate(fns, vars, depth):
        block = Block([], list(), list())
        block._generate(fns, vars, depth)
        return block

    def _generate(self, scope_fns, scope_vars, depth=0):
        size = sum(stmt.size for stmt in self.statements)

        while (
            size
            + (
                stmt := Statement.generate(
                    self.fns + scope_fns, self.vars + scope_vars, depth + 1
                )
            ).size
            < BLOCK_ASSIGNMENTS
        ):
            size += stmt.size
            self.statements.append(stmt)

            if isinstance(stmt, Function):
                self.fns.append(stmt.ident)
            elif isinstance(stmt, Assignment):
                self.vars.append(stmt.ident)


class Function(Statement):
    def __init__(self, ident, args: list[str], const: bool, block: Block, ret: str):
        super().__init__()

        self.ident = ident
        self.args = args
        self.const = const
        self.block = block
        self.ret = ret

    def compose(self) -> str:
        return (
            f"{self.ident} "
            + f":{':' if self.const else '='} "
            + f"fn {', '.join(self.args)} ->\n"
            + indented(f"{self.block._compose()}" + f"{self.ret}\n")
            + "end\n"
        )

    @staticmethod
    def generate(scope_fns, scope_vars, depth):
        ident = gen_id()
        const = random() > 0.5
        args = ["a"]
        block = Block.generate(scope_fns, scope_vars + args, depth + 1)
        ret = choice(block.vars + scope_vars)

        return Function(ident, args, const, block, ret)


class Root(Block):
    def __init__(self, statements, fns, vars):
        super().__init__(statements, fns, vars)

    def compose(self) -> str:
        return self._compose()

    def scramble(self):
        shuffle(self.statements)

    def add_start(self, block=Block([], list(), list())):
        self.statements.append(Function("start", [], True, block, ""))

    @staticmethod
    def generate():
        root = Root([], list(), list())
        root.add_start()

        root._generate(list(), list())

        return root


root = Root.generate()
print(root.compose())
with open("big_test.sy", "w") as file:
    file.write(root.compose())
