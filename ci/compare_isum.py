"""Cases and comparison for ci/compare_isum.sh: Lean and Rocq imaginary sums.

Usage:

    "$PYTHON" -I -B ci/compare_isum.py cases LEAN_FILE ROCQ_FILE ROCQ_MUTANT_FILE
    "$PYTHON" -I ci/compare_isum.py closure TARGET.v < DEP_OUTPUT
    "$PYTHON" -I -B ci/compare_isum.py compare LEAN_OUTPUT ROCQ_OUTPUT

`cases` writes a Lean program that prints the coordinates of Tower.isum of
lean/GororobaMath/CayleyDickson/ImaginarySum.lean over the integers at each level k from 1 to 6, one
line "k c_0 c_1 ..." per level with the 2^k coordinates in index order (first half, then second half,
recursively); a Rocq file that evaluates coord k (isum k) i of rocq/quantum/CdImaginarySumConference.v
on the same rows with vm_compute, one Eval per level; and a mutated Rocq reference, a copy of the
Fixpoint isum that drops the term one j from the second half.

`closure` reads the output of rocq dep on standard input and prints, in dependency order, the sources
of the directory that TARGET.v requires, TARGET.v last.

`compare` reads the rows each side printed (Rocq prints each Eval as "= [z; ...]", wrapped over lines,
followed by ": list Z") and exits 0 when both hold 6 rows of 126 coordinates and agree, 1 on the first
difference, and 2 when an output is unreadable or incomplete."""

import os
import re
import sys
from pathlib import Path

LEVELS = range(1, 7)
VALUES = sum(2**k for k in LEVELS)
EVAL = re.compile(r"^\s*=(.*?):\s*list Z", re.MULTILINE | re.DOTALL)
INT = re.compile(r"-?\d+")


def write_cases(lean_file: Path, rocq_file: Path, mutant_file: Path) -> None:
    lean = [
        "import GororobaMath.CayleyDickson.ImaginarySum",
        "",
        "open CayleyDickson",
        "",
        "def coords : (k : Nat) -> Tower Int k -> List Int",
        "  | 0, x => [x]",
        "  | k + 1, x => coords k x.re ++ coords k x.im",
        "",
        "def main : IO Unit := do",
        f"  for level in List.range {len(LEVELS)} do",
        "    let k := level + 1",
        '    IO.println s!"{k} {" ".intercalate ((coords k (Tower.isum Int k)).map toString)}"',
    ]
    lean_file.write_text("\n".join(lean) + "\n", encoding="utf-8")
    head = [
        "From Stdlib Require Import List ZArith.",
        "Require Import CdImaginarySumConference.",
        "Import ListNotations.",
        "",
    ]
    mutated = [
        "Fixpoint isum_mutant (k : nat) : cd k :=",
        "  match k as d return cd d with",
        "  | O => 0%Z",
        "  | S j => (isum_mutant j, isum_mutant j)",
        "  end.",
        "",
    ]
    for path, name, prefix in ((rocq_file, "isum", []), (mutant_file, "isum_mutant", mutated)):
        lines = head + prefix
        for k in LEVELS:
            lines.append(f"Eval vm_compute in map (coord {k} ({name} {k})) (seq 0 (Nat.pow 2 {k})).")
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


def read_lean(path: Path) -> list[list[int]]:
    rows = []
    for line in path.read_text(encoding="utf-8").splitlines():
        k, *values = line.split()
        rows.append([int(k)] + [int(v) for v in values])
    return rows


def read_rocq(path: Path) -> list[list[int]]:
    text = path.read_text(encoding="utf-8")
    return [[int(v) for v in INT.findall(m.group(1))] for m in EVAL.finditer(text)]


def compare(lean_path: Path, rocq_path: Path) -> int:
    try:
        lean = read_lean(lean_path)
        rocq = read_rocq(rocq_path)
    except (OSError, ValueError) as error:
        print(f"compare_isum: {error}", file=sys.stderr)
        return 2
    if len(lean) != len(LEVELS) or len(rocq) != len(LEVELS):
        print(
            f"compare_isum: expected {len(LEVELS)} rows, Lean printed {len(lean)}, Rocq {len(rocq)}",
            file=sys.stderr,
        )
        return 2
    for k, lean_row, rocq_row in zip(LEVELS, lean, rocq, strict=True):
        if lean_row[0] != k or not len(lean_row) - 1 == len(rocq_row) == 2**k:
            print(f"compare_isum: the row k={k} is malformed or out of order", file=sys.stderr)
            return 2
        for i, (a, b) in enumerate(zip(lean_row[1:], rocq_row, strict=True)):
            if a != b:
                print(f"compare_isum: k={k} coordinate {i}: Lean {a}, Rocq {b}", file=sys.stderr)
                return 1
    print(f"compare_isum: {VALUES} coordinates agree in Lean and Rocq at levels 1 to {LEVELS[-1]}")
    return 0


def main() -> int:
    args = sys.argv[1:]
    if len(args) == 4 and args[0] == "cases":
        write_cases(Path(args[1]), Path(args[2]), Path(args[3]))
        return 0
    if len(args) == 2 and args[0] == "closure":
        try:
            print("\n".join(closure(args[1], sys.stdin.read())))
        except ValueError as error:
            print(f"compare_isum: {error}", file=sys.stderr)
            return 2
        return 0
    if len(args) == 3 and args[0] == "compare":
        return compare(Path(args[1]), Path(args[2]))
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
