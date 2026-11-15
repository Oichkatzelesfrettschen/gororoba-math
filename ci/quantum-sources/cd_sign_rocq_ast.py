"""Serialize the syntax tree of cd_core.cd_sign as the Rocq term that rocq/quantum/CdSignPythonSemantics.v
evaluates.

ast.parse reads gororoba_quantum/cd_core.py of the gororoba-quantum checkout, and every node of the cd_sign
definition maps one to one onto a constructor of the Rocq syntax of that file: Name, Constant (int), BinOp (Sub,
RShift), UnaryOp (Not, USub), BoolOp (And), Compare with one operator (Eq, NotEq, Lt, LtE, Gt, GtE) and Call of a
bare name for expressions; Expr, Assign to one name, AugAssign of a name, If, While, Pass and Return for statements.
Any other node, a chained comparison, an else clause on a while loop, a keyword argument, a default or a variadic
parameter raises UnsupportedNode, so the Rocq term covers the whole function body. The leading docstring is the one
node dropped: a string literal that opens a function body becomes the function's __doc__ attribute (Python Language
Reference chapter 8, footnote 4) and runs no statement.

--check compares the generated term with the block between the BEGIN and END markers of each name in the .v file
and exits 1 on a difference, --write replaces those blocks, and with no flag the script prints the block for cd_sign.

Usage: GOROROBA_QUANTUM=PATH "$PYTHON" ci/quantum-sources/cd_sign_rocq_ast.py [--check | --write]
"""

from __future__ import annotations

import argparse
import ast
import sys

from quantum_checkout import ROCQ, ROOT

SOURCE = ROOT / "gororoba_quantum" / "cd_core.py"
PROOF = ROCQ / "CdSignPythonSemantics.v"

# The cd_sign branch that cd_phase_degree.py --mutate high-low-unconditional also replaces: the high-low case
# negates the sign whether or not q is zero. The Rocq file carries this mutant's term as a negative control.
MUTANT_OLD = "            if q != 0:\n                sign = -sign\n"
MUTANT_NEW = "            sign = -sign\n"

BINOPS: dict[type[ast.AST], str] = {ast.Sub: "Sub", ast.RShift: "RShift"}
UNARYOPS: dict[type[ast.AST], str] = {ast.Not: "Not", ast.USub: "USub"}
BOOLOPS: dict[type[ast.AST], str] = {ast.And: "And"}
CMPOPS: dict[type[ast.AST], str] = {
    ast.Eq: "Eq",
    ast.NotEq: "NotEq",
    ast.Lt: "Lt",
    ast.LtE: "LtE",
    ast.Gt: "Gt",
    ast.GtE: "GtE",
}


class UnsupportedNode(Exception):
    pass


def _string(text: str) -> str:
    if not text.isidentifier() or not text.isascii():
        raise UnsupportedNode(f"identifier {text!r} is not an ASCII Python identifier")
    return f'"{text}"'


def _list(items: list[str], indent: str) -> str:
    if not items:
        return "nil"
    return "(" + f" ::\n{indent}".join(items) + " ::\n" + indent + "nil)"


def _op(table: dict[type[ast.AST], str], op: ast.AST, what: str) -> str:
    name = table.get(type(op))
    if name is None:
        raise UnsupportedNode(f"{what} {type(op).__name__}")
    return name


def expr(node: ast.expr) -> str:
    if isinstance(node, ast.Name):
        return f"(Name {_string(node.id)})"
    if isinstance(node, ast.Constant):
        if isinstance(node.value, bool) or not isinstance(node.value, int):
            raise UnsupportedNode(f"constant {node.value!r}")
        return f"(Constant ({node.value})%Z)" if node.value < 0 else f"(Constant {node.value}%Z)"
    if isinstance(node, ast.BinOp):
        return f"(BinOp {expr(node.left)} {_op(BINOPS, node.op, 'binary operator')} {expr(node.right)})"
    if isinstance(node, ast.UnaryOp):
        return f"(UnaryOp {_op(UNARYOPS, node.op, 'unary operator')} {expr(node.operand)})"
    if isinstance(node, ast.BoolOp):
        values = " :: ".join(expr(value) for value in node.values)
        return f"(BoolOp {_op(BOOLOPS, node.op, 'boolean operator')} ({values} :: nil))"
    if isinstance(node, ast.Compare):
        if len(node.ops) != 1:
            raise UnsupportedNode("chained comparison")
        return f"(Compare {expr(node.left)} {_op(CMPOPS, node.ops[0], 'comparison')} {expr(node.comparators[0])})"
    if isinstance(node, ast.Call):
        if not isinstance(node.func, ast.Name) or node.keywords:
            raise UnsupportedNode("call of a non-name or with keywords")
        if any(isinstance(arg, ast.Starred) for arg in node.args):
            raise UnsupportedNode("starred call argument")
        args = " :: ".join(expr(arg) for arg in node.args)
        return f"(Call {_string(node.func.id)} ({args} :: nil))" if node.args else f"(Call {_string(node.func.id)} nil)"
    raise UnsupportedNode(f"expression {type(node).__name__}")


def _target(node: ast.expr) -> str:
    if not isinstance(node, ast.Name):
        raise UnsupportedNode(f"assignment target {type(node).__name__}")
    return _string(node.id)


def block(body: list[ast.stmt], indent: str) -> str:
    return _list([stmt(node, indent + "  ") for node in body], indent)


def stmt(node: ast.stmt, indent: str) -> str:
    if isinstance(node, ast.Expr):
        return f"Expr {expr(node.value)}"
    if isinstance(node, ast.Assign):
        if len(node.targets) != 1:
            raise UnsupportedNode("multiple assignment targets")
        return f"Assign {_target(node.targets[0])} {expr(node.value)}"
    if isinstance(node, ast.AugAssign):
        return f"AugAssign {_target(node.target)} {_op(BINOPS, node.op, 'binary operator')} {expr(node.value)}"
    if isinstance(node, ast.If):
        return f"If {expr(node.test)}\n{indent}{block(node.body, indent)}\n{indent}{block(node.orelse, indent)}"
    if isinstance(node, ast.While):
        if node.orelse:
            raise UnsupportedNode("while loop with an else clause")
        return f"While {expr(node.test)}\n{indent}{block(node.body, indent)}"
    if isinstance(node, ast.Pass):
        return "Pass"
    if isinstance(node, ast.Return):
        if node.value is None:
            raise UnsupportedNode("return without a value")
        return f"Return {expr(node.value)}"
    raise UnsupportedNode(f"statement {type(node).__name__}")


def function_term(source: str, name: str, definition: str) -> str:
    """The Rocq Definition of function `name` in `source`, named `definition`."""
    matches = [node for node in ast.parse(source).body if isinstance(node, ast.FunctionDef) and node.name == name]
    if len(matches) != 1:
        raise UnsupportedNode(f"{len(matches)} top-level definitions of {name}")
    (function,) = matches
    args = function.args
    if args.posonlyargs or args.vararg or args.kwonlyargs or args.kwarg or args.defaults or function.decorator_list:
        raise UnsupportedNode("parameters other than plain positional ones, or a decorator")
    body = function.body
    if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant):
        if isinstance(body[0].value.value, str):
            body = body[1:]
    params = " :: ".join(_string(arg.arg) for arg in args.args)
    return f"Definition {definition} : FunctionDef :=\n  mkFunctionDef ({params} :: nil)\n  {block(body, '  ')}.\n"


def terms(source: str) -> dict[str, str]:
    """The generated block for cd_sign and for its high-low-unconditional mutant, keyed by Rocq name."""
    if source.count(MUTANT_OLD) != 1:
        raise UnsupportedNode("the high-low guard of cd_sign is not unique in the source")
    return {
        "cd_sign_ast": function_term(source, "cd_sign", "cd_sign_ast"),
        "cd_sign_mutant_ast": function_term(source.replace(MUTANT_OLD, MUTANT_NEW), "cd_sign", "cd_sign_mutant_ast"),
    }


def _span(text: str, name: str) -> tuple[int, int]:
    begin, end = f"(* BEGIN {name}: generated by scripts/cd_sign_rocq_ast.py *)\n", f"(* END {name} *)"
    if text.count(begin) != 1 or text.count(end) != 1 or text.index(begin) > text.index(end):
        raise UnsupportedNode(f"markers of {name} missing, repeated or out of order in {PROOF.name}")
    return text.index(begin) + len(begin), text.index(end)


def embedded(text: str, name: str) -> str:
    start, stop = _span(text, name)
    return text[start:stop]


def replaced(text: str, generated: dict[str, str]) -> str:
    for name, term in generated.items():
        start, stop = _span(text, name)
        text = text[:start] + term + text[stop:]
    return text


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="compare the generated terms with the .v file")
    mode.add_argument("--write", action="store_true", help="replace the generated blocks of the .v file")
    options = parser.parse_args()
    generated = terms(SOURCE.read_text(encoding="utf-8"))
    proof = PROOF.read_text(encoding="utf-8")
    if options.write:
        PROOF.write_text(replaced(proof, generated), encoding="utf-8")
        return 0
    if not options.check:
        sys.stdout.write(generated["cd_sign_ast"])
        return 0
    stale = [name for name, term in generated.items() if embedded(proof, name) != term]
    if stale:
        print(f"{PROOF.name}: regenerate {', '.join(stale)} from {SOURCE.name}", file=sys.stderr)
        return 1
    print(f"{PROOF.name}: cd_sign_ast and cd_sign_mutant_ast match {SOURCE.name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
