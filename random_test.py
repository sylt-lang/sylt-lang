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

# Limit amount of assignments, since sylt compiles expressions to different assignments
# Lua only supports up to 200.
MAX_LUA_LOCALS = 20
# Limit nested expressions and functions
MAX_EXPR_DEPTH = 2
MAX_FN_DEPTH = 1

indented = lambda s: "".join(map(lambda ss: "  " + ss + "\n", s.splitlines()))  # noqa
current_var_number = 0
current_fn_number = 0


def gen_varname():
    global current_var_number
    current_var_number += 1
    return f"v{current_var_number}"


def gen_fnname():
    global current_fn_number
    current_fn_number += 1
    return f"f{current_fn_number}"


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
    def generate(scope_fns, scope_vars, expr_depth=0):
        if expr_depth >= MAX_EXPR_DEPTH:
            return Value.generate(scope_fns, scope_vars)
        else:
            return choice(
                [
                    lambda: Value.generate(scope_fns, scope_vars),
                    lambda: Operator.generate(scope_fns, scope_vars, expr_depth),
                ]
                + (
                    [lambda: FnCall.generate(scope_fns, scope_vars, expr_depth)]
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
    def generate(scope_fns, scope_vars, expr_depth):
        op = choice(["+", "-", "*"])
        lhs = Expression.generate(scope_fns, scope_vars, expr_depth + 1)
        rhs = Expression.generate(scope_fns, scope_vars, expr_depth + 1)
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
    def generate(scope_fns, scope_vars, expr_depth):
        return FnCall(
            choice(scope_fns),
            Expression.generate(scope_fns, scope_vars, expr_depth + 1),
        )


class Statement(Node):
    def __init__(self):
        super().__init__()

        self.size = 1

    def compose(self) -> str:
        raise NotImplementedError

    @staticmethod
    def generate(scope_fns, scope_vars, fn_depth=0):
        if fn_depth >= MAX_FN_DEPTH:
            return Assignment.generate(scope_fns, scope_vars)
        return choice(
            [
                lambda: Assignment.generate(scope_fns, scope_vars),
                lambda: Function.generate(scope_fns, scope_vars, fn_depth),
            ]
        )()


class Assignment(Statement):
    def __init__(self, ident, const: bool, expr: Expression):
        super().__init__()

        self.ident = ident
        self.const = const
        self.expr = expr

        self.size = expr.size()

    def compose(self) -> str:
        return f"{self.ident} :{':' if self.const else '='} {self.expr.compose()}\n"

    @staticmethod
    def generate(scope_fns, scope_vars):
        ident = gen_varname()
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
    def generate(fns, vars, fn_depth):
        block = Block([], list(), list())
        block._generate(fns, vars, fn_depth)
        return block

    def _generate(
        self, scope_fns, scope_vars, fn_depth=0, block_assignments=MAX_LUA_ASSIGNMENTS
    ):
        size = sum(stmt.size for stmt in self.statements)

        while (
            size
            + (
                stmt := Statement.generate(
                    self.fns + scope_fns, self.vars + scope_vars, fn_depth
                )
            ).size
            < block_assignments
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
    def generate(scope_fns, scope_vars, fn_depth):
        ident = gen_fnname()
        const = random() > 0.5
        arg = chr(ord("a") + fn_depth)
        args = [arg]
        block = Block.generate(scope_fns, scope_vars + args, fn_depth + 1)
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

        root._generate(list(), list(), 0, MAX_LUA_ASSIGNMENTS - 1)

        return root


root = Root.generate()
root.scramble()
print(root.compose())
with open("big_test.sy", "w") as file:
    file.write(root.compose())
