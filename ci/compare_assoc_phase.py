"""Cases and comparison for ci/compare_assoc_phase.sh: Lean, Rocq and Python associator phases.

Usage:

    "$PYTHON" -I -B ci/compare_assoc_phase.py import QUANTUM
    "$PYTHON" -I -B ci/compare_assoc_phase.py cases LEAN_FILE ROCQ_FILE ROCQ_MUTANT_FILE
    "$PYTHON" -I ci/compare_assoc_phase.py closure TARGET.v < DEP_OUTPUT
    "$PYTHON" -I -B ci/compare_assoc_phase.py compare QUANTUM LEAN_OUTPUT ROCQ_OUTPUT [--mutate-python]

QUANTUM is a gororoba-quantum checkout; the Python side imports predict.py from its gororoba_quantum
directory, which needs numpy. `import` exits 2 with a message when the import fails.

`cases` writes a Lean program that prints Tower.assocPhase p q x of
lean/GororobaMath/CayleyDickson/AssociatorPhase.lean for every triple of indices below 2^k at each level k
from 1 to 5, 37448 values, one line "k p q BITS" per pair p, q with the entry for x = 0, 1, ... as 1 when
the phase is true (the sign -1) and 0 otherwise; a Rocq file that evaluates assoc k p q x of
rocq/quantum/CdAssociatorAnf.v on the same rows with vm_compute, one Eval per row; and a mutated Rocq
reference with its last two arguments swapped (assoc k p x q).

`closure` reads the output of rocq dep on standard input and prints, in dependency order, the
sources of the directory that TARGET.v requires, TARGET.v last.

`compare` reads the rows each side printed (the Lean program prints one row per line; Rocq prints
each Eval as "= [b; ...]", wrapped over lines, followed by ": list bool"), computes the Python rows
(predict.associator_phase(2^k, p, q)[x] is -1), and exits 0 when all three hold 1364 rows of 37448 values and
agree, 1 on the first difference, and 2 when an output is unreadable or incomplete or the Python module does
not import. With --mutate-python the Python side negates the first entry of the first row, so the comparison
must exit 1. On agreement it prints the sha256 of each Python file read from the checkout.
"""

import hashlib
import importlib
import os
import re
import sys
from pathlib import Path

LEVELS = range(1, 6)
ROWS = [(k, p, q) for k in LEVELS for p in range(2**k) for q in range(2**k)]
VALUES = sum(8**k for k in LEVELS)
EVAL = re.compile(r"^\s*=(.*?):\s*list bool", re.MULTILINE | re.DOTALL)
BOOL = re.compile(r"true|false")


def load(quantum: Path):
    """Import predict from the checkout; exit status 2 when numpy or the module is missing."""
    sys.path.insert(0, str(quantum / "gororoba_quantum"))
    return importlib.import_module("predict")


def write_cases(lean_file: Path, rocq_file: Path, mutant_file: Path) -> None:
    lean = [
        "import GororobaMath.CayleyDickson.AssociatorPhase",
        "",
        "open CayleyDickson",
        "",
        "def main : IO Unit := do",
        f"  for level in List.range {len(LEVELS)} do",
        "    let k := level + 1",
        "    for p in List.range (2 ^ k) do",
        "      for q in List.range (2 ^ k) do",
        "        let row := (List.range (2 ^ k)).map fun x =>",
        '          if Tower.assocPhase (BitVec.ofNat k p) (BitVec.ofNat k q) (BitVec.ofNat k x) then "1" else "0"',
        '        IO.println s!"{k} {p} {q} {String.join row}"',
    ]
    lean_file.write_text("\n".join(lean) + "\n", encoding="utf-8")
    head = [
        "From Stdlib Require Import List.",
        "Require Import CdAssociatorAnf.",
        "Import ListNotations.",
        "",
    ]
    for path, call in ((rocq_file, "assoc {k} {p} {q} x"), (mutant_file, "assoc {k} {p} x {q}")):
        lines = list(head)
        for k, p, q in ROWS:
            lines.append(f"Eval vm_compute in map (fun x => {call.format(k=k, p=p, q=q)}) (seq 0 (Nat.pow 2 {k})).")
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


def python_rows(predict, mutate: bool) -> list[str]:
    rows = []
    for k, p, q in ROWS:
        phase = list(predict.associator_phase(2**k, p, q))
        if mutate and not rows:
            phase[0] = -phase[0]
        rows.append("".join("1" if value == -1 else "0" for value in phase))
    return rows


def read_lean(path: Path) -> list[tuple[int, int, int, str]]:
    rows = []
    for line in path.read_text(encoding="utf-8").splitlines():
        k, p, q, row = line.split()
        rows.append((int(k), int(p), int(q), row))
    return rows


def read_rocq(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    return ["".join("1" if v == "true" else "0" for v in BOOL.findall(m.group(1))) for m in EVAL.finditer(text)]


def read_files(quantum: Path) -> list[Path]:
    """The Python files of the checkout that the interpreter has loaded."""
    root = quantum / "gororoba_quantum"
    names = (getattr(m, "__file__", None) for m in sys.modules.values())
    return sorted({Path(n) for n in names if n and Path(n).is_relative_to(root)})


def compare(quantum: Path, lean_path: Path, rocq_path: Path, mutate: bool) -> int:
    try:
        predict = load(quantum)
        python = python_rows(predict, mutate)
        lean = read_lean(lean_path)
        rocq = read_rocq(rocq_path)
    except (ImportError, OSError, ValueError) as error:
        print(f"compare_assoc_phase: {error}", file=sys.stderr)
        return 2
    if len(lean) != len(ROWS) or len(rocq) != len(ROWS):
        print(
            f"compare_assoc_phase: expected {len(ROWS)} rows, Lean printed {len(lean)}, Rocq {len(rocq)}",
            file=sys.stderr,
        )
        return 2
    for (k, p, q), lean_row, rocq_row, python_row in zip(ROWS, lean, rocq, python, strict=True):
        if lean_row[:3] != (k, p, q) or not len(lean_row[3]) == len(rocq_row) == len(python_row) == 2**k:
            print(f"compare_assoc_phase: the row k={k} p={p} q={q} is malformed or out of order", file=sys.stderr)
            return 2
        for x, (a, b, c) in enumerate(zip(lean_row[3], rocq_row, python_row, strict=True)):
            if not a == b == c:
                print(
                    f"compare_assoc_phase: k={k} p={p} q={q} x={x}: Lean {a}, Rocq {b}, Python {c}",
                    file=sys.stderr,
                )
                return 1
    print(f"compare_assoc_phase: {VALUES} phases agree in Lean, Rocq and Python at levels 1 to {LEVELS[-1]}")
    for name in read_files(quantum):
        print(f"compare_assoc_phase: sha256 {hashlib.sha256(name.read_bytes()).hexdigest()} {name.name}")
    return 0


def main() -> int:
    args = sys.argv[1:]
    if len(args) == 2 and args[0] == "import":
        try:
            load(Path(args[1]))
        except ImportError as error:
            print(
                f"compare_assoc_phase: predict.py does not import ({error}); "
                "it needs numpy, so set PYTHON to an interpreter that has it",
                file=sys.stderr,
            )
            return 2
        return 0
    if len(args) == 4 and args[0] == "cases":
        write_cases(Path(args[1]), Path(args[2]), Path(args[3]))
        return 0
    if len(args) == 2 and args[0] == "closure":
        try:
            print("\n".join(closure(args[1], sys.stdin.read())))
        except ValueError as error:
            print(f"compare_assoc_phase: {error}", file=sys.stderr)
            return 2
        return 0
    if len(args) in (4, 5) and args[0] == "compare" and (len(args) == 4 or args[4] == "--mutate-python"):
        return compare(Path(args[1]), Path(args[2]), Path(args[3]), len(args) == 5)
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
