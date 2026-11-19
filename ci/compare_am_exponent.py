"""Cases and comparison for ci/compare_am_exponent.sh: Lean and Rocq cochain exponents.

Usage:

    "$PYTHON" -I -B ci/compare_am_exponent.py cases LEAN_FILE ROCQ_FILE ROCQ_MUTANT_FILE
    "$PYTHON" -I ci/compare_am_exponent.py closure TARGET.v < DEP_OUTPUT
    "$PYTHON" -I -B ci/compare_am_exponent.py compare LEAN_OUTPUT ROCQ_OUTPUT

`cases` writes a Lean program that prints Tower.amExponent k p q of
lean/GororobaMath/CayleyDickson/SignLaws.lean for every pair of indices below 2^k at each level k from
1 to 6, 5460 values, one line "k p BITS" per k and p with the entry for q = 0, 1, ... as 1 when the
exponent is true and 0 otherwise; a Rocq file that evaluates am_exponent k p q of
rocq/quantum/CdTowerBasisSign.v on the same rows with vm_compute, one Eval per row; and a mutated
Rocq reference, a copy of the Fixpoint with the two recursive arguments of its first branch exchanged.

`closure` reads the output of rocq dep on standard input and prints, in dependency order, the sources
of the directory that TARGET.v requires, TARGET.v last.

`compare` reads the rows each side printed (the Lean program prints one row per line; Rocq prints each
Eval as "= [b; ...]", wrapped over lines, followed by ": list bool") and exits 0 when both hold 126 rows
of 5460 values and agree, 1 on the first difference, and 2 when an output is unreadable or incomplete."""

import os
import re
import sys
from pathlib import Path

LEVELS = range(1, 7)
EVAL = re.compile(r"^\s*=(.*?):\s*list bool", re.MULTILINE | re.DOTALL)
BOOL = re.compile(r"true|false")
ROWS = [(k, p) for k in LEVELS for p in range(2**k)]
VALUES = sum(4**k for k in LEVELS)

def write_cases(lean_file: Path, rocq_file: Path, mutant_file: Path) -> None:
    lean = [
        "import GororobaMath.CayleyDickson.SignLaws",
        "",
        "open CayleyDickson",
        "",
        "def main : IO Unit := do",
        f"  for level in List.range {len(LEVELS)} do",
        "    let k := level + 1",
        "    for p in List.range (2 ^ k) do",
        "      let row := (List.range (2 ^ k)).map fun q =>",
        '        if Tower.amExponent k (BitVec.ofNat k p) (BitVec.ofNat k q) then "1" else "0"',
        '      IO.println s!"{k} {p} {String.join row}"',
    ]
    lean_file.write_text("\n".join(lean) + "\n", encoding="utf-8")
    head = [
        "From Stdlib Require Import List.",
        "Require Import CdTowerBasisSign.",
        "Import ListNotations.",
        "",
    ]
    mutated = [
        "Fixpoint am_mutant (k : nat) (x y : nat) : bool :=",
        "  match k with",
        "  | O => false",
        "  | S j =>",
        "      let h := Nat.pow 2 j in",
        "      let xh := Nat.leb h x in",
        "      let yh := Nat.leb h y in",
        "      let xl := if xh then (x - h)%nat else x in",
        "      let yl := if yh then (y - h)%nat else y in",
        "      xorb (if xh then am_mutant j xl yl else am_mutant j yl xl)",
        "        (xorb (andb yh (am_mutant j xl xl)) (andb xh yh))",
        "  end.",
        "",
    ]
    for path, name, prefix in ((rocq_file, "am_exponent", []), (mutant_file, "am_mutant", mutated)):
        lines = head + prefix
        for k, p in ROWS:
            lines.append(f"Eval vm_compute in map (fun q => {name} {k} {p} q) (seq 0 (Nat.pow 2 {k})).")
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


def read_lean(path: Path) -> list[tuple[int, int, str]]:
    rows = []
    for line in path.read_text(encoding="utf-8").splitlines():
        k, p, row = line.split()
        rows.append((int(k), int(p), row))
    return rows

def read_rocq(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    return ["".join("1" if v == "true" else "0" for v in BOOL.findall(m.group(1))) for m in EVAL.finditer(text)]

def compare(lean_path: Path, rocq_path: Path) -> int:
    try:
        lean = read_lean(lean_path)
        rocq = read_rocq(rocq_path)
    except (OSError, ValueError) as error:
        print(f"compare_am_exponent: {error}", file=sys.stderr)
        return 2
    if len(lean) != len(ROWS) or len(rocq) != len(ROWS):
        print(
            f"compare_am_exponent: expected {len(ROWS)} rows, Lean printed {len(lean)}, Rocq {len(rocq)}",
            file=sys.stderr,
        )
        return 2
    for (k, p), lean_row, rocq_row in zip(ROWS, lean, rocq, strict=True):
        if lean_row[:2] != (k, p) or not len(lean_row[2]) == len(rocq_row) == 2**k:
            print(f"compare_am_exponent: the row k={k} p={p} is malformed or out of order", file=sys.stderr)
            return 2
        for q, (a, b) in enumerate(zip(lean_row[2], rocq_row, strict=True)):
            if a != b:
                print(f"compare_am_exponent: k={k} p={p} q={q}: Lean {a}, Rocq {b}", file=sys.stderr)
                return 1
    print(f"compare_am_exponent: {VALUES} exponents agree in Lean and Rocq at levels 1 to {LEVELS[-1]}")
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
            print(f"compare_am_exponent: {error}", file=sys.stderr)
            return 2
        return 0
    if len(args) == 3 and args[0] == "compare":
        return compare(Path(args[1]), Path(args[2]))
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
