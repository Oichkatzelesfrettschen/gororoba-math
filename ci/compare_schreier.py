"""Cases and comparison for ci/compare_schreier.sh: Tower.schreier against schreier of SchreierSignCode.v.

Usage:

    "$PYTHON" -I ci/compare_schreier.py cases LEAN_FILE ROCQ_FILE ROCQ_MUTANT_FILE
    "$PYTHON" -I ci/compare_schreier.py compare LEAN_OUTPUT ROCQ_OUTPUT

`cases` writes a Lean program that prints, for each order 1 to 5 and each triple (l, r, x) of indices
below 2^order, the bit `Tower.schreier l r x` (GororobaMath.CayleyDickson.SignCode), a Rocq file that
prints the same bits of `schreier` of rocq/open/theories/SchreierSignCode.v with vm_compute, and a
mutated Rocq reference that swaps the first two arguments. The index m of order k is read as the
cube value whose component of rank j is bit j of m, the last pair component being the highest
bit, which is BitVec.ofNat k m on the Lean side. Triples run with l outermost and x innermost in
both files. `compare` reads the bits each side printed and exits 0 when both lists are equal and
nonempty, 1 on the first difference, and 2 when an output is unreadable.
"""

import re
import sys
from pathlib import Path

ORDERS = range(1, 6)


def write_cases(lean_file: Path, rocq_file: Path, mutant_file: Path) -> None:
    lean = [
        "import GororobaMath.CayleyDickson.SignCode",
        "",
        "open CayleyDickson",
        "",
        "def row (k : Nat) (l r : Nat) : String :=",
        "  String.join ((List.range (2 ^ k)).map fun x =>",
        "    if Tower.schreier (BitVec.ofNat k l) (BitVec.ofNat k r) (BitVec.ofNat k x) then \"1\\n\" else \"0\\n\")",
        "",
        "def main : IO Unit := do",
    ]
    for k in ORDERS:
        lean.append(f"  for l in List.range (2 ^ {k}) do")
        lean.append(f"    for r in List.range (2 ^ {k}) do")
        lean.append(f"      IO.print (row {k} l r)")
    lean_file.write_text("\n".join(lean) + "\n", encoding="utf-8")
    head = [
        "From Stdlib Require Import Bool Arith List.",
        "Require Import SchreierSignCode.",
        "Import ListNotations.",
        "",
        "Fixpoint of_nat (order : nat) (m : nat) : cube order :=",
        "  match order as d return cube d with",
        "  | O => tt",
        "  | S lower => (of_nat lower (m mod Nat.pow 2 lower), Nat.testbit m lower)",
        "  end.",
        "",
        "Definition triples (k : nat) : list (nat * nat * nat) :=",
        "  let n := Nat.pow 2 k in",
        "  flat_map (fun l => flat_map (fun r => map (fun x => (l, r, x)) (seq 0 n)) (seq 0 n)) (seq 0 n).",
        "",
        "Definition bit (b : bool) : nat := if b then 1 else 0.",
        "",
    ]
    for path, swap in ((rocq_file, False), (mutant_file, True)):
        lines = list(head)
        first, second = ("r", "l") if swap else ("l", "r")
        for k in ORDERS:
            lines.append(
                f"Eval vm_compute in map (fun t => let '(l, r, x) := t in "
                f"bit (schreier {k} (of_nat {k} {first}) (of_nat {k} {second}) (of_nat {k} x))) (triples {k})."
            )
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def read_lean(path: Path) -> list[int]:
    return [int(token) for token in path.read_text(encoding="utf-8").split()]


def read_rocq(path: Path) -> list[int]:
    text = path.read_text(encoding="utf-8")
    values = []
    for block in re.findall(r"=\s(.*?)\n\s+:\s", text, re.DOTALL):
        values.extend(int(token) for token in re.findall(r"\d+", block))
    return values


def main() -> int:
    if len(sys.argv) == 5 and sys.argv[1] == "cases":
        write_cases(Path(sys.argv[2]), Path(sys.argv[3]), Path(sys.argv[4]))
        return 0
    if len(sys.argv) == 4 and sys.argv[1] == "compare":
        try:
            lean = read_lean(Path(sys.argv[2]))
            rocq = read_rocq(Path(sys.argv[3]))
        except (OSError, ValueError) as error:
            print(f"compare_schreier: {error}", file=sys.stderr)
            return 2
        expected = sum(8**k for k in ORDERS)
        if len(lean) != expected or len(rocq) != expected:
            print(
                f"compare_schreier: expected {expected} values, Lean printed {len(lean)}, Rocq {len(rocq)}",
                file=sys.stderr,
            )
            return 2
        for index, (a, b) in enumerate(zip(lean, rocq, strict=True)):
            if a != b:
                print(f"compare_schreier: value {index} differs: Lean {a}, Rocq {b}", file=sys.stderr)
                return 1
        print(f"compare_schreier: {expected} values agree")
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
