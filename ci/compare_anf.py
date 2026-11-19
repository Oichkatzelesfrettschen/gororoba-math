"""Cases and comparison for ci/compare_anf.sh: Lean, Rocq and Python algebraic normal forms.

Usage:

    "$PYTHON" -I -B ci/compare_anf.py import QUANTUM
    "$PYTHON" -I -B ci/compare_anf.py cases QUANTUM LEAN_FILE ROCQ_FILE ROCQ_MUTANT_FILE ROCQ_DEGREE_MUTANT_FILE
    "$PYTHON" -I ci/compare_anf.py closure TARGET.v < DEP_OUTPUT
    "$PYTHON" -I -B ci/compare_anf.py compare QUANTUM LEAN_OUTPUT ROCQ_OUTPUT [--mutate-python | --mutate-python-degree]

QUANTUM is a gororoba-quantum checkout; the Python side imports boolean_anf.py and
cd_core.py from its gororoba_quantum directory. `import` checks that boolean_anf and cd_core import.

The tables are every truth table on 0, 1, 2 and 3 variables (278 tables) and the sign rows
x -> [cd_sign(2^k, x, m) = -1] for every m below 2^k at the levels k = 3, 4 and 5 (8 + 16 + 32
tables), each as the integer T whose bit x is the entry at x. `cases` writes a Lean program
that prints, for every table, the row "coef k T BITS" of Tower.anfCoeff of
lean/GororobaMath/CayleyDickson/BooleanAnf.lean the row "eval k T BITS" of Tower.anfEval at the
coefficient table, BITS the 2^k entries as 0 and 1 from index 0, and the row "deg k T D" of Tower.anfDegree,
D a decimal number; a Rocq file that evaluates anf_coef and anf_eval of rocq/quantum/CdSignRowAnf.v and
anf_degree of rocq/quantum/CdAssociatorCensus.v with vm_compute on the same tables, each read from its N
literal with N.testbit, one Eval per row; a mutated Rocq reference whose submask test is reversed; and a
mutated Rocq reference whose degree skips the monomial of every variable.

`closure` reads the output of rocq dep on standard input and prints, in dependency order, the
sources of the directory that TARGET.v requires, TARGET.v last.

`compare` reads the rows each side printed (the Lean program prints one row per line; Rocq prints
each Eval as "= [b; ...]", wrapped over lines, followed by ": list bool"), computes the Python rows
(anf_coefficients, then evaluate_anf at every input of the masks it returned, then anf_degree), and exits 0 when all three
agree on every row and every eval row equals its truth table, 1 on the first difference, and 2 when an
output is unreadable or incomplete or the Python modules do not import. With --mutate-python the Python
side toggles the coefficient of the mask 0 in the first table with a variable, and with
--mutate-python-degree it adds 1 to the degree of that table; each comparison must exit 1. On agreement it prints the sha256 of each Python file read from the checkout.
"""

import hashlib
import importlib
import os
import re
import sys
from pathlib import Path

TRUTH_VARIABLES = range(4)
SIGN_LEVELS = range(3, 6)
EVAL = re.compile(r"^\s*=(.*?):\s*(list bool|nat)\b", re.MULTILINE | re.DOTALL)
NUMBER = re.compile(r"\d+")
BOOL = re.compile(r"true|false")


def load(quantum: Path):
    """Import boolean_anf and cd_core from the checkout; return both modules."""
    sys.path.insert(0, str(quantum / "gororoba_quantum"))
    return importlib.import_module("boolean_anf"), importlib.import_module("cd_core")


def tables(cd_core) -> list[tuple[int, int]]:
    result = []
    for n in TRUTH_VARIABLES:
        result.extend((n, t) for t in range(2 ** (2**n)))
    for k in SIGN_LEVELS:
        size = 2**k
        for m in range(size):
            result.append((k, sum(1 << x for x in range(size) if cd_core.cd_sign(size, x, m) == -1)))
    return result


def bits(table: int, k: int) -> str:
    return "".join(str((table >> x) & 1) for x in range(2**k))


def write_cases(
    table_list: list[tuple[int, int]], lean_file: Path, rocq_file: Path, mutant_file: Path, degree_mutant_file: Path
) -> None:
    pairs = ", ".join(f"({k}, {t})" for k, t in table_list)
    lean = [
        "import GororobaMath.CayleyDickson.BooleanAnf",
        "",
        "open CayleyDickson",
        "",
        "def table (k t : Nat) : BitVec k → Bool := fun x => t.testBit x.toNat",
        "",
        "def bits (k : Nat) (g : BitVec k → Bool) : String :=",
        '  String.join ((List.range (2 ^ k)).map fun x => if g (BitVec.ofNat k x) then "1" else "0")',
        "",
        f"def cases : List (Nat × Nat) := [{pairs}]",
        "",
        "def main : IO Unit := do",
        "  for (k, t) in cases do",
        "    let coef := Tower.anfCoeff (table k t)",
        '    IO.println s!"coef {k} {t} {bits k coef}"',
        '    IO.println s!"eval {k} {t} {bits k (Tower.anfEval coef)}"',
        '    IO.println s!"deg {k} {t} {Tower.anfDegree (table k t)}"',
    ]
    lean_file.write_text("\n".join(lean) + "\n", encoding="utf-8")
    head = [
        "From Stdlib Require Import List NArith.",
        "Require Import CdSignRowAnf CdAssociatorCensus.",
        "Import ListNotations.",
        "",
        "Definition tab (t : N) (x : nat) : bool := N.testbit t (N.of_nat x).",
        "",
    ]
    reference = [
        "Definition anf_coef_ref (k : nat) (f : nat -> bool) (s : nat) : bool := anf_coef k f s.",
        "Definition anf_eval_ref (k : nat) (c : nat -> bool) (x : nat) : bool := anf_eval k c x.",
        "Definition anf_degree_ref (k : nat) (f : nat -> bool) : nat := anf_degree k f.",
        "",
    ]
    mutant = [
        "Definition subset_rev (t s : nat) : bool := subset s t.",
        "Definition anf_coef_ref (k : nat) (f : nat -> bool) (s : nat) : bool :=",
        "  xsum k (fun t => andb (subset_rev t s) (f t)).",
        "Definition anf_eval_ref (k : nat) (c : nat -> bool) (x : nat) : bool :=",
        "  xsum k (fun s => andb (subset_rev s x) (c s)).",
        "Definition anf_degree_ref (k : nat) (f : nat -> bool) : nat := anf_degree k f.",
        "",
    ]
    degree_mutant = [
        "Definition anf_coef_ref (k : nat) (f : nat -> bool) (s : nat) : bool := anf_coef k f s.",
        "Definition anf_eval_ref (k : nat) (c : nat -> bool) (x : nat) : bool := anf_eval k c x.",
        "Definition anf_degree_ref (k : nat) (f : nat -> bool) : nat :=",
        "  max_weight k f (Nat.pred (Nat.pow 2 k)).",
        "",
    ]
    for path, body in ((rocq_file, reference), (mutant_file, mutant), (degree_mutant_file, degree_mutant)):
        lines = head + body
        for k, t in table_list:
            f = f"(tab {t}%N)"
            lines.append(f"Eval vm_compute in map (fun s => anf_coef_ref {k} {f} s) (seq 0 (Nat.pow 2 {k})).")
            lines.append(
                f"Eval vm_compute in map (fun x => anf_eval_ref {k} (anf_coef_ref {k} {f}) x) (seq 0 (Nat.pow 2 {k}))."
            )
            lines.append(f"Eval vm_compute in anf_degree_ref {k} {f}.")
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def closure(target: str, dep_output: str) -> list[str]:
    deps: dict[str, list[str]] = {}
    for line in dep_output.replace("\\\n", " ").splitlines():
        if ":" not in line:
            continue
        lhs, rhs = line.split(":", 1)
        objects = [t for t in lhs.split() if t.endswith(".vo")]
        if not objects:
            continue
        source = os.path.normpath(objects[0][:-3] + ".v")
        required = [os.path.normpath(t[:-3] + ".v") for t in rhs.split() if t.endswith(".vo")]
        deps[source] = [r for r in required if r != source]
    target = os.path.normpath(target)
    if target not in deps:
        raise ValueError(f"rocq dep lists no {target}")
    order: list[str] = []
    seen: set[str] = set()

    def visit(source: str) -> None:
        if source in seen:
            return
        seen.add(source)
        for dep in deps.get(source, []):
            visit(dep)
        order.append(source)

    visit(target)
    missing = [s for s in order if s not in deps]
    if missing:
        raise ValueError(f"the closure of {target} needs sources outside the directory: {missing}")
    return order


def python_rows(anf, table_list: list[tuple[int, int]], mutate: str) -> list[tuple[str, int, int, str]]:
    rows = []
    mutated = False
    for k, t in table_list:
        truth = [(t >> x) & 1 for x in range(2**k)]
        masks = anf.anf_coefficients(truth)
        degree = anf.anf_degree(truth)
        if mutate and not mutated and k >= 1:
            if mutate == "coefficient":
                masks = tuple(sorted(set(masks) ^ {0}))
            else:
                degree += 1
            mutated = True
        selected = set(masks)
        rows.append(("coef", k, t, "".join("1" if s in selected else "0" for s in range(2**k))))
        rows.append(("eval", k, t, "".join(str(anf.evaluate_anf(masks, x)) for x in range(2**k))))
        rows.append(("deg", k, t, str(degree)))
    return rows


def read_lean(path: Path) -> list[tuple[str, int, int, str]]:
    rows = []
    for line in path.read_text(encoding="utf-8").splitlines():
        kind, k, t, row = line.split()
        rows.append((kind, int(k), int(t), row))
    return rows


def read_rocq(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    return [
        NUMBER.search(m.group(1)).group() if m.group(2) == "nat" else "".join("1" if v == "true" else "0" for v in BOOL.findall(m.group(1)))
        for m in EVAL.finditer(text)
    ]


def read_files(quantum: Path) -> list[Path]:
    """The Python files of the checkout that the interpreter has loaded."""
    root = quantum / "gororoba_quantum"
    names = (getattr(m, "__file__", None) for m in sys.modules.values())
    return sorted({Path(n) for n in names if n and Path(n).is_relative_to(root)})


def compare(quantum: Path, lean_path: Path, rocq_path: Path, mutate: str) -> int:
    try:
        anf, cd_core = load(quantum)
        table_list = tables(cd_core)
        python = python_rows(anf, table_list, mutate)
        lean = read_lean(lean_path)
        rocq = read_rocq(rocq_path)
    except (ImportError, OSError, ValueError) as error:
        print(f"compare_anf: {error}", file=sys.stderr)
        return 2
    if len(lean) != len(python) or len(rocq) != len(python):
        print(
            f"compare_anf: expected {len(python)} rows, Lean printed {len(lean)}, Rocq {len(rocq)}",
            file=sys.stderr,
        )
        return 2
    status = 0
    for (kind, k, t, expected), lean_row, rocq_row in zip(python, lean, rocq, strict=True):
        width = 2**k if kind != "deg" else len(expected)
        if lean_row[:3] != (kind, k, t) or not len(lean_row[3]) == len(rocq_row) == len(expected) == width:
            print(f"compare_anf: the {kind} row of k={k} table={t} is malformed or out of order", file=sys.stderr)
            return 2
        if not lean_row[3] == rocq_row == expected:
            print(
                f"compare_anf: {kind} k={k} table={t}: Lean {lean_row[3]}, Rocq {rocq_row}, Python {expected}",
                file=sys.stderr,
            )
            status = 1
            break
        if kind == "eval" and expected != bits(t, k):
            print(
                f"compare_anf: eval k={k} table={t}: the evaluation {expected} is not the truth table {bits(t, k)}",
                file=sys.stderr,
            )
            status = 1
            break
    if status:
        return status
    print(f"compare_anf: {len(table_list)} tables, {len(python)} rows (coefficients, evaluations, degrees) agree in Lean, Rocq and Python")
    for name in read_files(quantum):
        print(f"compare_anf: sha256 {hashlib.sha256(name.read_bytes()).hexdigest()} {name.name}")
    return 0


def main() -> int:
    args = sys.argv[1:]
    if len(args) == 2 and args[0] == "import":
        try:
            load(Path(args[1]))
        except ImportError as error:
            print(f"compare_anf: the Python reference does not import: {error}", file=sys.stderr)
            return 2
        return 0
    if len(args) == 6 and args[0] == "cases":
        try:
            _, cd_core = load(Path(args[1]))
        except ImportError as error:
            print(f"compare_anf: the Python reference does not import: {error}", file=sys.stderr)
            return 2
        write_cases(tables(cd_core), Path(args[2]), Path(args[3]), Path(args[4]), Path(args[5]))
        return 0
    if len(args) == 2 and args[0] == "closure":
        try:
            print("\n".join(closure(args[1], sys.stdin.read())))
        except ValueError as error:
            print(f"compare_anf: {error}", file=sys.stderr)
            return 2
        return 0
    flags = {"--mutate-python": "coefficient", "--mutate-python-degree": "degree"}
    if len(args) in (4, 5) and args[0] == "compare" and (len(args) == 4 or args[4] in flags):
        return compare(Path(args[1]), Path(args[2]), Path(args[3]), flags[args[4]] if len(args) == 5 else "")
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
