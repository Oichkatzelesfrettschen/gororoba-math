"""Cases and comparison for ci/compare_aligned_pair_count.sh: the Lean and Rocq aligned-pair counts.

Usage:

    "$PYTHON" -I ci/compare_aligned_pair_count.py cases LEAN_FILE ROCQ_FILE ROCQ_MUTANT_FILE
    "$PYTHON" -I ci/compare_aligned_pair_count.py closure TARGET.v < DEP_OUTPUT
    "$PYTHON" -I ci/compare_aligned_pair_count.py compare LEAN_OUTPUT ROCQ_OUTPUT

`cases` writes a Lean program that prints Tower.alignedPairCount k i j of
lean/GororobaMath/CayleyDickson/TwoTerm.lean for every pair of indices i, j below
2^k at each level k from 0 to 7, one line "k i N_0 ... N_(2^k - 1)" per row i; a
Rocq file that evaluates TwoTermRecursion.aligned_pair_count of
rocq/quantum/CdTowerTwoTermRecursion.v on the same rows with vm_compute, one
Eval per row; and a mutated Rocq reference that counts only the indices with
aligned_add and drops aligned_sub.

`closure` reads the output of rocq dep on standard input and prints, in
dependency order, the sources of the directory that TARGET.v requires, TARGET.v
last.

`compare` reads the rows each side printed (the Lean program prints one row
per line; Rocq prints each Eval as "= [N_0; ...; N_m]", wrapped over lines, followed by
": list nat"; the list notation keeps a row of 128 entries within the printing depth, which
elides the nested form of a long cons chain)
and exits 0 when both hold the 255 rows of the 21845 pairs and agree, 1 on the
first difference, and 2 when an output is unreadable or incomplete.
"""

import os
import re
import sys
from pathlib import Path

LEVELS = range(8)
ROWS = [(k, i) for k in LEVELS for i in range(2**k)]
PAIRS = sum(4**k for k in LEVELS)
EVAL = re.compile(r"^\s*=(.*?):\s*list nat", re.MULTILINE | re.DOTALL)
NUMBER = re.compile(r"[0-9]+")


def write_cases(lean_file: Path, rocq_file: Path, mutant_file: Path) -> None:
    lean = [
        "import GororobaMath.CayleyDickson.TwoTerm",
        "",
        "open CayleyDickson",
        "",
        "def main : IO Unit := do",
        f"  for k in List.range {len(LEVELS)} do",
        "    for i in List.range (2 ^ k) do",
        "      let row := (List.range (2 ^ k)).map fun j =>",
        "        Tower.alignedPairCount k (BitVec.ofNat k i) (BitVec.ofNat k j)",
        '      IO.println (" ".intercalate ((k :: i :: row).map toString))',
    ]
    lean_file.write_text("\n".join(lean) + "\n", encoding="utf-8")
    head = [
        "From Stdlib Require Import List.",
        "Require Import CdTowerTwoTermBridge CdTowerTwoTermRecursion.",
        "Import ListNotations.",
        "",
    ]
    count = [
        "Definition count (k i j : nat) : nat := TwoTermRecursion.aligned_pair_count k i j.",
        "",
    ]
    mutant = [
        "Definition count (k i j : nat) : nat :=",
        "  if Nat.eqb i j then O",
        "  else Nat.div (length (filter (fun x => IntegerTwoTermBridge.aligned_add k i j x) (seq 0 (Nat.pow 2 k)))) 2.",
        "",
    ]
    for path, body in ((rocq_file, count), (mutant_file, mutant)):
        lines = head + body
        for k, i in ROWS:
            lines.append(f"Eval vm_compute in map (fun j => count {k} {i} j) (seq 0 (Nat.pow 2 {k})).")
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


def read_lean(path: Path) -> dict[tuple[int, int], list[int]]:
    rows = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        values = [int(v) for v in line.split()]
        if len(values) < 2:
            raise ValueError(f"short Lean row {line!r}")
        rows[(values[0], values[1])] = values[2:]
    return rows


def read_rocq(path: Path) -> list[list[int]]:
    rows = []
    for match in EVAL.finditer(path.read_text(encoding="utf-8")):
        rows.append([int(v) for v in NUMBER.findall(match.group(1))])
    return rows


def compare(lean_path: Path, rocq_path: Path) -> int:
    try:
        lean = read_lean(lean_path)
        rocq = read_rocq(rocq_path)
    except (OSError, ValueError) as error:
        print(f"compare_aligned_pair_count: {error}", file=sys.stderr)
        return 2
    if sorted(lean) != ROWS or len(rocq) != len(ROWS):
        print(
            f"compare_aligned_pair_count: expected {len(ROWS)} rows, Lean printed {len(lean)}, Rocq {len(rocq)}",
            file=sys.stderr,
        )
        return 2
    for (k, i), row in zip(ROWS, rocq, strict=True):
        if len(lean[(k, i)]) != 2**k or len(row) != 2**k:
            print(f"compare_aligned_pair_count: row k={k} i={i} is not of length {2**k}", file=sys.stderr)
            return 2
        for j, (a, b) in enumerate(zip(lean[(k, i)], row, strict=True)):
            if a != b:
                print(f"compare_aligned_pair_count: k={k} i={i} j={j}: Lean {a}, Rocq {b}", file=sys.stderr)
                return 1
    print(f"compare_aligned_pair_count: {PAIRS} counts agree at levels 0 to {LEVELS[-1]}")
    return 0


def main() -> int:
    if len(sys.argv) == 5 and sys.argv[1] == "cases":
        write_cases(Path(sys.argv[2]), Path(sys.argv[3]), Path(sys.argv[4]))
        return 0
    if len(sys.argv) == 3 and sys.argv[1] == "closure":
        try:
            print("\n".join(closure(sys.argv[2], sys.stdin.read())))
        except ValueError as error:
            print(f"compare_aligned_pair_count: {error}", file=sys.stderr)
            return 2
        return 0
    if len(sys.argv) == 4 and sys.argv[1] == "compare":
        return compare(Path(sys.argv[2]), Path(sys.argv[3]))
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
