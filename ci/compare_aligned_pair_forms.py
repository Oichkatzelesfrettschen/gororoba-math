"""Cases and comparison for ci/compare_aligned_pair_forms.sh: four Lean definitions and their Rocq partners.

Usage:

    "$PYTHON" -I ci/compare_aligned_pair_forms.py cases LEAN_FILE ROCQ_FILE ROCQ_MUTANT_FILE
    "$PYTHON" -I ci/compare_aligned_pair_forms.py compare LEAN_OUTPUT ROCQ_OUTPUT
    "$PYTHON" -I ci/compare_aligned_pair_forms.py reject LEAN_OUTPUT ROCQ_MUTANT_OUTPUT

The definitions are, Lean first and the Rocq partner second:

- M: Tower.alignedPairCountMultiplicity k n of AlignedPairSpectrum.lean and
  AlignedPairSpectrum.multiplicity k n of rocq/quantum/CdTowerAlignedPairSpectrum.v,
  for every level k from 0 to 5 and every n from 0 to 16.
- F, C, D: Tower.closedForm k i j, Tower.clearedXorBit and Tower.DegenerateSplit of
  AlignedPairClosedForm.lean and closed_form, cleared_xor_bit and degenerate_split of
  rocq/quantum/CdTowerAlignedPairClosedForm.v, on every pair i, j below 2^k at the levels
  0 to 6; C reads the cleared bits s < k as the index sum of 2^s over the kept bits, D the
  degenerate splits p < k as the index sum of 2^p.
- P: Tower.clearedXorParity i j t and cleared_xor_parity k i j t of the same files, on
  every pair i, j below 2^k at the levels 0 to 5 and every t from 0 to k, so the positions
  t = 0, 1 and 2 that the closed form never reads are compared too.
- A: Tower.associates a b c of AssociatorSpace.lean and AssociatorSign.associates k a b c
  of rocq/quantum/CdTowerAssociatorSpace.v, as 0 or 1, on every triple below 2^k at the
  levels 0 to 5.
- B, G: KernelMap.binContract k i j pos of KernelMap/TwoTermBins.lean and
  TwoTermBins.bin_contract of rocq/quantum/CdTowerTwoTermBins.v, as 0 or 1, on every pair
  i, j below 2^k: B on every labelling L at the levels 0 to 3, with pos x bit x of L, in
  blocks of 64 labellings; G at the levels 4 and 5 on the contract labelling (+1 at every
  aligned index and at the smaller index of each misaligned pair, written in each program
  from Tower.misaligned and Tower.partner) and on its 2^k one-bin mutations, m = 0 the
  labelling itself and m = x + 1 the labelling with bin x flipped.

cases writes a Lean program that prints one line "CODE PARAMS... VALUES..." per row, a
Rocq file that evaluates the same rows with vm_compute, one Eval per row, and a mutated
Rocq reference: a multiplicity over the pairs i < j only, a cleared bit that keeps every
bit of i XOR j (and the closed form built on it), a degenerate split without the clause
that the low part of j is zero, an associativity sign that reads e_b e_c for e_c e_b, and
a bin contract without the clause that an aligned bin is +1, and a parity complemented at
t = 0, 1 and 2, where the closed form does not read it.

compare exits 0 when both outputs hold every row and agree, 1 on the first difference,
and 2 when an output is unreadable or incomplete. reject exits 0 when every table of the
mutated reference differs from the Lean output, 1 when a table agrees, and 2 as compare.
The shell script runs reject first and compare only after the mutant is rejected.
"""

import re
import sys
from pathlib import Path

CODES = {"M": 0, "F": 1, "C": 2, "D": 3, "A": 4, "B": 5, "G": 6, "P": 7}
NAMES = {v: k for k, v in CODES.items()}
# The number of leading fields of a printed row that name it: the code and the row parameters.
HEAD_SIZE = {0: 2, 1: 3, 2: 3, 3: 3, 4: 4, 5: 5, 6: 4, 7: 4}
EVAL = re.compile(r"^\s*=(.*?):\s*list nat", re.MULTILINE | re.DOTALL)
NUMBER = re.compile(r"[0-9]+")
BLOCK = 64


def rows() -> list[tuple[int, ...]]:
    """The row heads in printing order: the code of the table and the row parameters."""
    out: list[tuple[int, ...]] = [(CODES["M"], k) for k in range(6)]
    for k in range(7):
        for i in range(2**k):
            out += [(CODES["F"], k, i), (CODES["C"], k, i), (CODES["D"], k, i)]
    for k in range(6):
        out += [(CODES["A"], k, a, b) for a in range(2**k) for b in range(2**k)]
    for k in range(4):
        blocks = max(1, 2 ** (2**k) // BLOCK)
        out += [(CODES["B"], k, i, j, n) for i in range(2**k) for j in range(2**k) for n in range(blocks)]
    for k in (4, 5):
        out += [(CODES["G"], k, i, j) for i in range(2**k) for j in range(2**k)]
    for k in range(6):
        out += [(CODES["P"], k, i, j) for i in range(2**k) for j in range(2**k)]
    return out


ROWS = rows()


def width(head: tuple[int, ...]) -> int:
    code, k = head[0], head[1]
    if code == CODES["M"]:
        return 17
    if code == CODES["B"]:
        return min(BLOCK, 2 ** (2**k))
    if code == CODES["G"]:
        return 2**k + 1
    if code == CODES["P"]:
        return k + 1
    return 2**k


LEAN = """import GororobaMath.CayleyDickson.AlignedPairSpectrum
import GororobaMath.CayleyDickson.AlignedPairClosedForm
import GororobaMath.CayleyDickson.AssociatorSpace
import GororobaMath.KernelMap.TwoTermBins

open CayleyDickson

def out (head row : List Nat) : IO Unit :=
  IO.println (" ".intercalate ((head ++ row).map toString))

def bv (k i : Nat) : BitVec k := BitVec.ofNat k i

def clearedIndex (k i j : Nat) : Nat :=
  ((List.range k).map fun s => if Tower.clearedXorBit (bv k i) (bv k j) s then 2 ^ s else 0).sum

def degenerateIndex (k i j : Nat) : Nat :=
  ((List.range k).map fun p => if Tower.DegenerateSplit (bv k i) (bv k j) p then 2 ^ p else 0).sum

def ideal (k i j x : Nat) : Bool :=
  !Tower.misaligned k (bv k i) (bv k j) (bv k x) || decide (x < (Tower.partner (bv k i) (bv k j) (bv k x)).toNat)

def labelled (k i j m : Nat) (x : BitVec k) : Bool :=
  if m == x.toNat + 1 then !ideal k i j x.toNat else ideal k i j x.toNat

def main : IO Unit := do
  for k in List.range 6 do
    out [0, k] ((List.range 17).map fun n => Tower.alignedPairCountMultiplicity k n)
  for k in List.range 7 do
    for i in List.range (2 ^ k) do
      out [1, k, i] ((List.range (2 ^ k)).map fun j => Tower.closedForm k (bv k i) (bv k j))
      out [2, k, i] ((List.range (2 ^ k)).map fun j => clearedIndex k i j)
      out [3, k, i] ((List.range (2 ^ k)).map fun j => degenerateIndex k i j)
  for k in List.range 6 do
    for a in List.range (2 ^ k) do
      for b in List.range (2 ^ k) do
        out [4, k, a, b] ((List.range (2 ^ k)).map fun c => (Tower.associates (bv k a) (bv k b) (bv k c)).toNat)
  for k in List.range 4 do
    for i in List.range (2 ^ k) do
      for j in List.range (2 ^ k) do
        for n in List.range (max 1 (2 ^ (2 ^ k) / BLOCK)) do
          out [5, k, i, j, n] ((List.range (min BLOCK (2 ^ (2 ^ k)))).map fun r =>
            (KernelMap.binContract k (bv k i) (bv k j) fun x => Nat.testBit (BLOCK * n + r) x.toNat).toNat)
  for k in [4, 5] do
    for i in List.range (2 ^ k) do
      for j in List.range (2 ^ k) do
        out [6, k, i, j] ((List.range (2 ^ k + 1)).map fun m =>
          (KernelMap.binContract k (bv k i) (bv k j) (labelled k i j m)).toNat)
  for k in List.range 6 do
    for i in List.range (2 ^ k) do
      for j in List.range (2 ^ k) do
        out [7, k, i, j] ((List.range (k + 1)).map fun t => Tower.clearedXorParity (bv k i) (bv k j) t)
"""

ROCQ_HEAD = """From Stdlib Require Import List Bool.
Require Import CdTowerBasisBridge CdTowerTwoTermBridge CdTowerTwoTermRecursion CdTowerAlignedPairSpectrum.
Require Import CdTowerAlignedPairClosedForm CdTowerAssociatorSpace CdTowerTwoTermBins.
Import ListNotations.

Definition b2 (b : bool) : nat := if b then 1 else 0.
"""

ROCQ_DEFS = """Definition mult (k n : nat) : nat := AlignedPairSpectrum.multiplicity k n.
Definition cbit (k i j s : nat) : bool := AlignedPairClosedForm.cleared_xor_bit k i j s.
Definition cf (k i j : nat) : nat := AlignedPairClosedForm.closed_form k i j.
Definition dsplit (i j p : nat) : bool := AlignedPairClosedForm.degenerate_split i j p.
Definition par (k i j t : nat) : nat := AlignedPairClosedForm.cleared_xor_parity k i j t.
Definition assoc (k a b c : nat) : bool := AssociatorSign.associates k a b c.
Definition contract (k i j : nat) (pos : nat -> bool) : bool := TwoTermBins.bin_contract k i j pos.
"""

ROCQ_MUTANT_DEFS = """Definition mult (k n : nat) : nat :=
  TwoTermRecursion.nsum (Nat.pow 2 k) (fun i => TwoTermRecursion.nsum (Nat.pow 2 k) (fun j =>
    if Nat.ltb i j then TwoTermRecursion.ind (Nat.eqb (TwoTermRecursion.aligned_pair_count k i j) n) else 0)).
Definition cbit (k i j s : nat) : bool := xorb (Nat.testbit i s) (Nat.testbit j s).
Definition cf (k i j : nat) : nat :=
  4 * AlignedPairClosedForm.isum 3 k (fun t => Nat.pow 2 (k - 1 - t) *
    Nat.modulo (AlignedPairClosedForm.isum t k (fun s => TwoTermRecursion.ind (cbit k i j s))) 2).
Definition par (k i j t : nat) : nat :=
  if Nat.ltb t 3 then 1 - AlignedPairClosedForm.cleared_xor_parity k i j t
  else AlignedPairClosedForm.cleared_xor_parity k i j t.
Definition dsplit (i j p : nat) : bool :=
  negb (Bool.eqb (Nat.testbit i p) (Nat.testbit j p)) &&
  (forallb (fun s => negb (Nat.testbit i s)) (seq 0 p) ||
   forallb (fun s => Bool.eqb (Nat.testbit i s) (Nat.testbit j s)) (seq 0 p)).
Definition assoc (k a b c : nat) : bool :=
  Bool.eqb (xorb (TowerSign.neg_sign k a c) (TowerSign.neg_sign k (Nat.lxor a c) b))
    (xorb (TowerSign.neg_sign k b c) (TowerSign.neg_sign k a (Nat.lxor c b))).
Definition contract (k i j : nat) (pos : nat -> bool) : bool :=
  forallb (fun x => if TwoTermRecursion.misaligned k i j x
    then negb (Bool.eqb (pos (IntegerTwoTermBridge.partner i j x)) (pos x)) else true) (seq 0 (Nat.pow 2 k)).
"""

ROCQ_TAIL = """Definition cleared_index (k i j : nat) : nat :=
  fold_right Nat.add 0 (map (fun s => if cbit k i j s then Nat.pow 2 s else 0) (seq 0 k)).
Definition degenerate_index (k i j : nat) : nat :=
  fold_right Nat.add 0 (map (fun p => if dsplit i j p then Nat.pow 2 p else 0) (seq 0 k)).
Definition ideal (k i j x : nat) : bool :=
  orb (negb (TwoTermRecursion.misaligned k i j x)) (Nat.ltb x (IntegerTwoTermBridge.partner i j x)).
Definition labelled (k i j m x : nat) : bool := if Nat.eqb m (S x) then negb (ideal k i j x) else ideal k i j x.
"""


def rocq_eval(head: tuple[int, ...]) -> str:
    code, k = NAMES[head[0]], head[1]
    seq = f"(seq 0 {width(head)})"
    if code == "M":
        body = f"map (fun n => mult {k} n) {seq}"
    elif code == "F":
        body = f"map (fun j => cf {k} {head[2]} j) {seq}"
    elif code == "C":
        body = f"map (fun j => cleared_index {k} {head[2]} j) {seq}"
    elif code == "D":
        body = f"map (fun j => degenerate_index {k} {head[2]} j) {seq}"
    elif code == "A":
        body = f"map (fun c => b2 (assoc {k} {head[2]} {head[3]} c)) {seq}"
    elif code == "B":
        base = BLOCK * head[4]
        body = f"map (fun r => b2 (contract {k} {head[2]} {head[3]} (fun x => Nat.testbit ({base} + r) x))) {seq}"
    elif code == "P":
        body = f"map (fun t => par {k} {head[2]} {head[3]} t) {seq}"
    else:
        body = f"map (fun m => b2 (contract {k} {head[2]} {head[3]} (labelled {k} {head[2]} {head[3]} m))) {seq}"
    return f"Eval vm_compute in {body}."


def write_cases(lean_file: Path, rocq_file: Path, mutant_file: Path) -> None:
    lean_file.write_text(LEAN.replace("BLOCK", str(BLOCK)), encoding="utf-8")
    evals = "\n".join(rocq_eval(head) for head in ROWS) + "\n"
    rocq_file.write_text(ROCQ_HEAD + ROCQ_DEFS + ROCQ_TAIL + evals, encoding="utf-8")
    mutant_file.write_text(ROCQ_HEAD + ROCQ_MUTANT_DEFS + ROCQ_TAIL + evals, encoding="utf-8")


def read_lean(path: Path) -> dict[tuple[int, ...], list[int]]:
    table = {}
    lengths = {head: len(head) for head in ROWS}
    for line in path.read_text(encoding="utf-8").splitlines():
        values = [int(v) for v in line.split()]
        if len(values) < 2:
            raise ValueError(f"short Lean row {line!r}")
        size = HEAD_SIZE.get(values[0], 0)
        head = tuple(values[:size])
        if lengths.get(head) != size:
            raise ValueError(f"unexpected Lean row {line[:60]!r}")
        table[head] = values[size:]
    return table


def read_rocq(path: Path) -> list[list[int]]:
    return [[int(v) for v in NUMBER.findall(m.group(1))] for m in EVAL.finditer(path.read_text(encoding="utf-8"))]


def differences(lean_path: Path, rocq_path: Path) -> dict[str, str]:
    """The first difference of each table, keyed by table name; raises ValueError on an incomplete output."""
    lean = read_lean(lean_path)
    rocq = read_rocq(rocq_path)
    if sorted(lean) != sorted(ROWS) or len(rocq) != len(ROWS):
        raise ValueError(f"expected {len(ROWS)} rows, Lean printed {len(lean)}, Rocq {len(rocq)}")
    found: dict[str, str] = {}
    for head, row in zip(ROWS, rocq, strict=True):
        if len(lean[head]) != width(head) or len(row) != width(head):
            raise ValueError(f"row {head} is not of length {width(head)}")
        name = NAMES[head[0]]
        if name in found:
            continue
        for column, (a, b) in enumerate(zip(lean[head], row, strict=True)):
            if a != b:
                found[name] = f"table {name} row {head[1:]} column {column}: Lean {a}, Rocq {b}"
                break
    return found


def main() -> int:
    if len(sys.argv) == 5 and sys.argv[1] == "cases":
        write_cases(Path(sys.argv[2]), Path(sys.argv[3]), Path(sys.argv[4]))
        return 0
    if len(sys.argv) == 4 and sys.argv[1] in ("compare", "reject"):
        try:
            found = differences(Path(sys.argv[2]), Path(sys.argv[3]))
        except (OSError, ValueError) as error:
            print(f"compare_aligned_pair_forms: {error}", file=sys.stderr)
            return 2
        if sys.argv[1] == "compare":
            for text in found.values():
                print(f"compare_aligned_pair_forms: {text}", file=sys.stderr)
                return 1
            print(f"compare_aligned_pair_forms: {len(ROWS)} rows of the tables {', '.join(CODES)} agree")
            return 0
        accepted = [name for name in CODES if name not in found]
        if accepted:
            print(f"compare_aligned_pair_forms: the mutated reference agrees on table {accepted[0]}", file=sys.stderr)
            return 1
        print(f"compare_aligned_pair_forms: the mutated reference differs on every table ({', '.join(CODES)})")
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
