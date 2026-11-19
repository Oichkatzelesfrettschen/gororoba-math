"""Cases and comparison for ci/compare_open_tree.sh: the open-tree ANF and associator phase.

Usage:

    "$PYTHON" -I -B ci/compare_open_tree.py cases LEAN_FILE ROCQ_DIR
    "$PYTHON" -I -B ci/compare_open_tree.py compare PART LEAN_OUTPUT ROCQ_OUTPUT

PART is `anf` or `assoc`. `cases` writes a Lean program and, into ROCQ_DIR, the Rocq evaluation files
of rocq/open/theories/BooleanANFDegree.v (`CompareOpenAnf.v`, `CompareOpenAnfMutant.v`,
`CompareOpenAnfDegreeMutant.v`) and of rocq/open/theories/CDAssociatorDoubling.v
(`CompareOpenAssoc.v`, `CompareOpenAssocMutant.v`).

The ANF tables are every truth table on 0, 1, 2 and 3 variables (278 tables), a bent function
and 64 xorshift tables on 4 variables, and 32 xorshift tables on 5 variables, each as the integer T
whose bit x is the entry at index x. For each table the Lean program prints one row of the 2^k
coefficients `Tower.anfCoeff`, the 2^k values of `Tower.anfEval` at that coefficient table and the
degree `Tower.anfDegree` (GororobaMath.CayleyDickson.BooleanAnf); the Rocq file prints the same numbers
from `anf_evaluate` (the canonical ANF), `anf_evaluate` applied to the canonical ANF, and `anf_degree`,
one `Eval vm_compute` per variable count. The index m of order k is read as the cube value whose component
of rank j is bit j of m, the last pair component being the highest bit, which is BitVec.ofNat k m
on the Lean side. The associator phase is compared on every triple (p, q, x) below 2^k at the orders 1 to 5
(37448 triples, p outermost and x innermost): `Tower.assocPhase p q x` of
GororobaMath.CayleyDickson.AssociatorPhase against `associator_phase k p q x`. The mutated Rocq
references use a coefficient transform whose upper half reads the lower half of the table, a degree one
smaller than `anf_degree` and the last two arguments of the phase swapped.

`compare` reads the numbers each side printed (the Lean program separates the two parts with a line of
dashes) and exits 0 when the part agrees on every number and the counts match, 1 on the first difference,
and 2 when an output is unreadable or incomplete.
"""

import re
import sys
from pathlib import Path

ORDERS = range(1, 6)
SPLIT = re.compile(r"=\s(.*?)\n\s+:\s", re.DOTALL)


def tables() -> list[tuple[int, int]]:
    """Return the (variable count, table integer) cases."""
    cases = [(k, t) for k in range(4) for t in range(2 ** (2**k))]
    bent = 0
    for x in range(16):
        bit = ((x & 1) & ((x >> 1) & 1)) ^ (((x >> 2) & 1) & ((x >> 3) & 1))
        bent |= bit << x
    cases.append((4, bent))
    for k, count in ((4, 64), (5, 32)):
        state = 0x9E3779B9 + k
        for _ in range(count):
            table = 0
            for x in range(2**k):
                state ^= (state << 13) & 0xFFFFFFFF
                state ^= state >> 17
                state ^= (state << 5) & 0xFFFFFFFF
                table |= (state & 1) << x
            cases.append((k, table))
    return cases


def rocq_head(extra: str) -> list[str]:
    return [
        "From Stdlib Require Import Bool Arith List.",
        "From OpenGororoba Require Import SchreierSignCode BooleanANFDegree CDAssociatorDoubling.",
        "Import ListNotations.",
        "",
        "Fixpoint of_nat (order : nat) (m : nat) : cube order :=",
        "  match order as d return cube d with",
        "  | O => tt",
        "  | S lower => (of_nat lower (m mod Nat.pow 2 lower), Nat.testbit m lower)",
        "  end.",
        "",
        "Fixpoint to_nat (order : nat) : cube order -> nat :=",
        "  match order as d return cube d -> nat with",
        "  | O => fun _ => 0",
        "  | S lower => fun value => to_nat lower (fst value) + (if snd value then Nat.pow 2 lower else 0)",
        "  end.",
        "",
        "Definition bit (b : bool) : nat := if b then 1 else 0.",
        "",
        extra,
    ]


MUTANT_ANF = [
    "Fixpoint anf_mutant (order : nat) : (cube order -> bool) -> cube order -> bool :=",
    "  match order with",
    "  | O => fun coefficients _ => coefficients tt",
    "  | S lower => fun coefficients input =>",
    "      xorb (anf_mutant lower (fun mask => coefficients (mask, false)) (fst input))",
    "        (andb (snd input) (anf_mutant lower (fun mask => coefficients (mask, false)) (fst input)))",
    "  end.",
]


def write_anf(path: Path, transform: str, degree: str, extra: list[str]) -> None:
    lines = rocq_head("\n".join(extra))
    lines += [
        "",
        "Definition table (l : list nat) (order : nat) : cube order -> bool :=",
        "  fun value => Nat.eqb (nth (to_nat order value) l 0) 1.",
        "",
        "Definition row (order : nat) (l : list nat) : list nat :=",
        f"  let coef := {transform} order (table l order) in",
        "  map (fun m => bit (coef (of_nat order m))) (seq 0 (Nat.pow 2 order)) ++",
        f"  map (fun m => bit ({transform} order coef (of_nat order m))) (seq 0 (Nat.pow 2 order)) ++",
        f"  [{degree} order (table l order)].",
        "",
    ]
    cases = tables()
    for k in range(4 + 2):
        rows = ["[" + "; ".join(str((t >> x) & 1) for x in range(2**k)) + "]" for order, t in cases if order == k]
        if rows:
            lines.append(f"Eval vm_compute in map (row {k}) [{'; '.join(rows)}].")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_assoc(path: Path, first: str, second: str) -> None:
    lines = rocq_head("")
    lines += [
        "Definition triples (k : nat) : list (nat * nat * nat) :=",
        "  let n := Nat.pow 2 k in",
        "  flat_map (fun l => flat_map (fun r => map (fun x => (l, r, x)) (seq 0 n)) (seq 0 n)) (seq 0 n).",
        "",
    ]
    for k in ORDERS:
        lines.append(
            f"Eval vm_compute in map (fun t => let '(l, r, x) := t in "
            f"bit (associator_phase {k} (of_nat {k} l) (of_nat {k} {first}) (of_nat {k} {second}))) (triples {k})."
        )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_cases(lean_file: Path, rocq_dir: Path) -> None:
    lean = [
        "import GororobaMath.CayleyDickson.BooleanAnf",
        "import GororobaMath.CayleyDickson.AssociatorPhase",
        "",
        "open CayleyDickson",
        "",
        "def table (k t : Nat) : BitVec k -> Bool := fun x => t.testBit x.toNat",
        "",
        'def bits (l : List Bool) : String := String.join (l.map fun b => if b then "1 " else "0 ")',
        "",
        "def anfRow (k t : Nat) : String :=",
        "  let f := table k t",
        "  bits ((List.range (2 ^ k)).map fun m => Tower.anfCoeff f (BitVec.ofNat k m)) ++",
        "  bits ((List.range (2 ^ k)).map fun m => Tower.anfEval (Tower.anfCoeff f) (BitVec.ofNat k m)) ++",
        '  toString (Tower.anfDegree f) ++ "\\n"',
        "",
        "def assocRow (k l r : Nat) : String :=",
        "  String.join ((List.range (2 ^ k)).map fun x =>",
        '    if Tower.assocPhase (BitVec.ofNat k l) (BitVec.ofNat k r) (BitVec.ofNat k x) then "1\\n" else "0\\n")',
        "",
        "def main : IO Unit := do",
    ]
    for k, t in tables():
        lean.append(f"  IO.print (anfRow {k} {t})")
    lean.append('  IO.println "---"')
    for k in ORDERS:
        lean.append(f"  for l in List.range (2 ^ {k}) do")
        lean.append(f"    for r in List.range (2 ^ {k}) do")
        lean.append(f"      IO.print (assocRow {k} l r)")
    lean_file.write_text("\n".join(lean) + "\n", encoding="utf-8")
    write_anf(rocq_dir / "CompareOpenAnf.v", "anf_evaluate", "anf_degree", [])
    write_anf(rocq_dir / "CompareOpenAnfMutant.v", "anf_mutant", "anf_degree", MUTANT_ANF)
    write_anf(
        rocq_dir / "CompareOpenAnfDegreeMutant.v",
        "anf_evaluate",
        "anf_degree_mutant",
        ["Definition anf_degree_mutant order (function : cube order -> bool) := Nat.pred (anf_degree order function)."],
    )
    write_assoc(rocq_dir / "CompareOpenAssoc.v", "r", "x")
    write_assoc(rocq_dir / "CompareOpenAssocMutant.v", "x", "r")


def read_lean(path: Path, part: str) -> list[int]:
    text = path.read_text(encoding="utf-8")
    anf, assoc = text.split("---\n")
    return [int(token) for token in (anf if part == "anf" else assoc).split()]


def read_rocq(path: Path) -> list[int]:
    text = path.read_text(encoding="utf-8")
    values: list[int] = []
    for block in SPLIT.findall(text):
        values.extend(int(token) for token in re.findall(r"\d+", block))
    return values


def main() -> int:
    if len(sys.argv) == 4 and sys.argv[1] == "cases":
        write_cases(Path(sys.argv[2]), Path(sys.argv[3]))
        return 0
    if len(sys.argv) == 5 and sys.argv[1] == "compare" and sys.argv[2] in ("anf", "assoc"):
        part = sys.argv[2]
        try:
            lean = read_lean(Path(sys.argv[3]), part)
            rocq = read_rocq(Path(sys.argv[4]))
        except (OSError, ValueError) as error:
            print(f"compare_open_tree: {error}", file=sys.stderr)
            return 2
        if part == "anf":
            expected = sum(2 * 2**k + 1 for k, _ in tables())
        else:
            expected = sum(8**k for k in ORDERS)
        if len(lean) != expected or len(rocq) != expected:
            print(
                f"compare_open_tree: {part}: expected {expected} values, Lean printed {len(lean)}, Rocq {len(rocq)}",
                file=sys.stderr,
            )
            return 2
        for index, (a, b) in enumerate(zip(lean, rocq, strict=True)):
            if a != b:
                print(f"compare_open_tree: {part}: value {index} differs: Lean {a}, Rocq {b}", file=sys.stderr)
                return 1
        print(f"compare_open_tree: {part}: {expected} values agree")
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
