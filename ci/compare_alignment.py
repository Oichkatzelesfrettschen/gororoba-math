"""Cases and comparison for ci/compare_alignment.sh: the Lean and Rocq alignment tables.

Usage:

    "$PYTHON" -I ci/compare_alignment.py cases LEAN_FILE ROCQ_FILE MUTANT_FILE...
    "$PYTHON" -I ci/compare_alignment.py compare LEAN_OUTPUT ROCQ_OUTPUT

The cases command writes a Lean program that prints, for each level k from 0 to
6, the code of every triple (i, j, x) with i, j and x below 2^k, in the order
of i first, then j, then x, as one line of space-separated integers per level.
The code of a triple is partner + 64 * alignedAdd + 128 * alignedSub, where
partner, alignedAdd and alignedSub are CayleyDickson.Tower.partner,
CayleyDickson.Tower.alignedAdd and CayleyDickson.Tower.alignedSub of
lean/GororobaMath/CayleyDickson/TwoTerm.lean on the bit vectors of value i, j
and x, and a Boolean contributes its weight when it is true. It writes a Rocq
file that evaluates the same code with vm_compute from
IntegerTwoTermBridge.partner, .aligned_add and .aligned_sub of
rocq/quantum/CdTowerTwoTermBridge.v, and three mutated Rocq references
(partner without its second operand, aligned_add without the negation of its
first conjunct, aligned_sub with the argument order of one neg_sign call
swapped), each of which prints the same tables. Every table holds
sum over k of 8^k = 299593 codes.

The compare command reads the integers each side printed (the Lean program
prints one line per level; Rocq prints each Eval as a string of two hex digits
per code followed by ": string") and exits 0 when the levels are equal entry by
entry, 1 on the first difference, and 2 when an output is unreadable or has
the wrong shape.
"""

import re
import sys
from pathlib import Path

LEVELS = range(7)
ENTRIES = sum(8**k for k in LEVELS)
ADD_WEIGHT = 64
SUB_WEIGHT = 128
BLOCK = re.compile(r'^\s*=\s*"(.*?)"\s*\n\s*:\s*string\s*$', re.DOTALL | re.MULTILINE)

LEAN = """import GororobaMath.CayleyDickson.TwoTerm

open CayleyDickson.Tower

def code (k i j x : Nat) : Nat :=
  let a := BitVec.ofNat k i
  let b := BitVec.ofNat k j
  let c := BitVec.ofNat k x
  (partner a b c).toNat + (if alignedAdd k a b c then 64 else 0) +
    (if alignedSub k a b c then 128 else 0)

def row (k : Nat) : String := Id.run do
  let n := 2 ^ k
  let mut parts : Array String := #[]
  for i in [0:n] do
    for j in [0:n] do
      for x in [0:n] do
        parts := parts.push (toString (code k i j x))
  return " ".intercalate parts.toList

def main : IO Unit := do
  for k in [0:7] do
    IO.println (row k)
"""

ROCQ_HEAD = """From Stdlib Require Import List PeanoNat Ascii String.
Require Import CdTowerBasisBridge CdTowerTwoTermBridge.
Import TowerSign.

Module I := IntegerTwoTermBridge.

Definition table (code : nat -> nat -> nat -> nat -> nat) (k : nat) : list nat :=
  let n := Nat.pow 2 k in
  flat_map (fun i => flat_map (fun j => map (fun x => code k i j x) (seq 0 n)) (seq 0 n)) (seq 0 n).

Definition weight (b : bool) (w : nat) : nat := if b then w else 0.

Definition hex_digit (n : nat) : Ascii.ascii :=
  Ascii.ascii_of_nat (if Nat.ltb n 10 then 48 + n else 87 + n).

Definition hex_text (l : list nat) : String.string :=
  fold_right (fun c acc => String.String (hex_digit (Nat.div c 16)) (String.String (hex_digit (Nat.modulo c 16)) acc))
    String.EmptyString l.

"""

REFERENCE = """Definition code (k i j x : nat) : nat :=
  I.partner i j x + weight (I.aligned_add k i j x) 64 + weight (I.aligned_sub k i j x) 128.
"""

# Each mutant keeps the shape of the reference and changes one operation.
MUTANTS = [
    """Definition partner_m (i j x : nat) : nat := Nat.lxor x i.
Definition add_m (k i j x : nat) : bool :=
  andb (negb (Bool.eqb (neg_sign k i x) (neg_sign k j (partner_m i j x))))
    (negb (Bool.eqb (neg_sign k j x) (neg_sign k i (partner_m i j x)))).
Definition sub_m (k i j x : nat) : bool :=
  andb (Bool.eqb (neg_sign k i x) (neg_sign k j (partner_m i j x)))
    (Bool.eqb (neg_sign k j x) (neg_sign k i (partner_m i j x))).
""",
    """Definition partner_m (i j x : nat) : nat := I.partner i j x.
Definition add_m (k i j x : nat) : bool :=
  andb (Bool.eqb (neg_sign k i x) (neg_sign k j (partner_m i j x)))
    (negb (Bool.eqb (neg_sign k j x) (neg_sign k i (partner_m i j x)))).
Definition sub_m (k i j x : nat) : bool := I.aligned_sub k i j x.
""",
    """Definition partner_m (i j x : nat) : nat := I.partner i j x.
Definition add_m (k i j x : nat) : bool := I.aligned_add k i j x.
Definition sub_m (k i j x : nat) : bool :=
  andb (Bool.eqb (neg_sign k i x) (neg_sign k j (partner_m i j x)))
    (Bool.eqb (neg_sign k (partner_m i j x) j) (neg_sign k i (partner_m i j x))).
""",
]

MUTANT_CODE = """Definition code (k i j x : nat) : nat :=
  partner_m i j x + weight (add_m k i j x) 64 + weight (sub_m k i j x) 128.
"""


def rocq_file(definitions: str) -> str:
    lines = [ROCQ_HEAD + definitions]
    lines.extend(f"Eval vm_compute in hex_text (table code {k})." for k in LEVELS)
    return "\n".join(lines) + "\n"


def write_cases(lean_file: Path, rocq_path: Path, mutant_files: list[Path]) -> None:
    lean_file.write_text(LEAN, encoding="utf-8")
    rocq_path.write_text(rocq_file(REFERENCE), encoding="utf-8")
    for path, mutant in zip(mutant_files, MUTANTS, strict=True):
        path.write_text(rocq_file(mutant + MUTANT_CODE), encoding="utf-8")


def read_lean(path: Path) -> list[list[int]]:
    return [[int(v) for v in line.split()] for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def read_rocq(path: Path) -> list[list[int]]:
    text = path.read_text(encoding="utf-8")
    tables = []
    for m in BLOCK.finditer(text):
        digits = "".join(m.group(1).split())
        if len(digits) % 2:
            raise ValueError("a Rocq table has an odd number of hex digits")
        tables.append([int(digits[n : n + 2], 16) for n in range(0, len(digits), 2)])
    return tables


def first_difference(level: int, lean: list[int], rocq: list[int]) -> str | None:
    size = 2**level
    for index, (a, b) in enumerate(zip(lean, rocq, strict=True)):
        if a != b:
            i, rest = divmod(index, size * size)
            j, x = divmod(rest, size)
            return (
                f"level {level} i={i} j={j} x={x}: Lean code {a} "
                f"(partner {a % 64}, add {(a // ADD_WEIGHT) % 2}, sub {(a // SUB_WEIGHT) % 2}), Rocq code {b}"
            )
    return None


def main() -> int:
    if len(sys.argv) >= 5 and sys.argv[1] == "cases":
        write_cases(Path(sys.argv[2]), Path(sys.argv[3]), [Path(p) for p in sys.argv[4:]])
        return 0
    if len(sys.argv) == 4 and sys.argv[1] == "compare":
        try:
            lean = read_lean(Path(sys.argv[2]))
            rocq = read_rocq(Path(sys.argv[3]))
        except (OSError, ValueError) as error:
            print(f"compare_alignment: {error}", file=sys.stderr)
            return 2
        shape = [8**k for k in LEVELS]
        if [len(t) for t in lean] != shape or [len(t) for t in rocq] != shape:
            print(
                f"compare_alignment: expected tables of sizes {shape}, "
                f"Lean printed {[len(t) for t in lean]}, Rocq {[len(t) for t in rocq]}",
                file=sys.stderr,
            )
            return 2
        for level, (a, b) in enumerate(zip(lean, rocq, strict=True)):
            difference = first_difference(level, a, b)
            if difference is not None:
                print(f"compare_alignment: {difference}", file=sys.stderr)
                return 1
        print(f"compare_alignment: {ENTRIES} triples (levels 0 to 6) agree in partner, alignedAdd and alignedSub")
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
