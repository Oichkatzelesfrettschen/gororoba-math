"""Inputs and comparison for ci/compare_estimator_rocq.sh.

`cases LEAN_OUT ROCQ_OUT MUTANT_OUT` writes twelve fixed blocks of the nullity
estimator (the shapes of ci/compare_estimator.py, with every bin decided and
a bin-dependent rational contrast drawn from a fixed formula, no random draw)
as three programs that read identical rationals:

- a Lean program that prints vHat, nHat, nullity, vBarPos and vBarNeg of
  lean/GororobaMath/KernelMap/Estimator.lean over the rationals;
- a Rocq program that instantiates Defs of rocq/quantum/KernelMapEstimator.v
  with the QArith operations and prints the same five readings;
- the same Rocq program with its nHat replaced by the estimate formed with
  the unsigned mean of the contrast in place of the signed visibility.

`compare LEAN_OUTPUT ROCQ_OUTPUT MUTANT_OUTPUT` parses the readings, requires
Lean and Rocq to agree exactly on every block, and requires the same
comparison to reject the mutant on at least one block.

Exit status: 0 agreement and the mutant rejected, 1 a difference or an
accepted mutant, 2 a usage error.
"""

import re
import sys
from fractions import Fraction
from pathlib import Path

# (bins, indices of the bins with ideal contrast -1); the shapes of
# ci/compare_estimator.py.
BLOCKS = (
    (4, ()),
    (4, (1,)),
    (4, (0, 3)),
    (8, ()),
    (8, (2,)),
    (8, (1, 4, 6)),
    (8, (0, 1, 2, 3)),
    (16, ()),
    (16, (5, 9)),
    (16, (0, 3, 6, 9, 12, 15)),
    (16, (1, 2, 4, 7, 8, 11, 13, 14)),
    (32, (3, 17, 30)),
)
Block = list[tuple[bool, Fraction]]
READINGS = ("vHat", "nHat", "nullity", "vBarPos", "vBarNeg")


def contrast(case: int, y: int, negative: bool) -> Fraction:
    """Observed contrast of bin y: the ideal sign times a decaying weight, plus a bin-dependent leak."""
    weight = Fraction(11 + (2 * y + case) % 5, 16)
    leak = Fraction((5 * y + 3 * case) % 7 - 3, 40)
    return (-weight if negative else weight) + leak


def blocks() -> list[Block]:
    result = []
    for case, (bins, negative) in enumerate(BLOCKS):
        block = [(y not in negative, contrast(case, y, y in negative)) for y in range(bins)]
        signed = sum(c if positive else -c for positive, c in block)
        if signed <= 0:
            raise SystemExit(f"compare_estimator_rocq: block {case} has a non-positive signed visibility")
        result.append(block)
    return result


def lean_program(all_blocks: list[Block]) -> str:
    rows = []
    for block in all_blocks:
        entries = ", ".join(
            f"({'true' if positive else 'false'}, (({c.numerator} : ℚ) / {c.denominator}))" for positive, c in block
        )
        rows.append(f"  [{entries}]")
    return (
        "import GororobaMath.KernelMap.Estimator\n\nopen KernelMap\n\n"
        "def blocks : List (List (Bool × ℚ)) := [\n" + ",\n".join(rows) + "\n]\n\n"
        "def main : IO Unit := do\n"
        "  for block in blocks do\n"
        "    let bins := Finset.range block.length\n"
        "    let contrast : ℕ → ℚ := fun y => (block.getD y (false, 0)).2\n"
        "    let positive : ℕ → Prop := fun y => (block.getD y (false, 0)).1 = true\n"
        '    IO.println s!"{vHat bins contrast positive} {nHat bins contrast positive} '
        "{nullity (K := ℚ) bins positive} {vBarPos bins contrast positive} "
        '{vBarNeg bins contrast positive}"\n'
    )


def rocq_program(all_blocks: list[Block], mutant: bool) -> str:
    rows = []
    for block in all_blocks:
        entries = "; ".join(
            f"({'true' if positive else 'false'}, Qmake ({c.numerator})%Z {c.denominator}%positive)"
            for positive, c in block
        )
        rows.append(f"  [{entries}]")
    n_hat = "nHat_unsigned b" if mutant else "D.nHat (seq 0 (length b)) (cc b) (pp b)"
    return (
        "From Stdlib Require Import QArith List ZArith.\n"
        "Import ListNotations.\n"
        "Require Import KernelMapEstimator.\n\n"
        "Module QOps <: FieldOps.\n"
        "  Definition t := Q.\n"
        "  Definition zero : t := 0%Q.\n"
        "  Definition one : t := 1%Q.\n"
        "  Definition add : t -> t -> t := Qplus.\n"
        "  Definition mul : t -> t -> t := Qmult.\n"
        "  Definition sub : t -> t -> t := Qminus.\n"
        "  Definition opp : t -> t := Qopp.\n"
        "  Definition inv : t -> t := Qinv.\n"
        "  Definition div : t -> t -> t := Qdiv.\n"
        "End QOps.\n\n"
        "Module D := Defs QOps.\n\n"
        "Definition blocks : list (list (bool * Q)) := [\n" + ";\n".join(rows) + "\n].\n\n"
        "Definition cc (b : list (bool * Q)) (y : nat) : Q := snd (nth y b (false, 0%Q)).\n"
        "Definition pp (b : list (bool * Q)) (y : nat) : bool := fst (nth y b (false, 0%Q)).\n\n"
        "Definition nHat_unsigned (b : list (bool * Q)) : Q :=\n"
        "  let bins := seq 0 (length b) in\n"
        "  Qdiv (Qdiv (D.sum (cc b) bins) 2) (Qdiv (D.sum (cc b) bins) (inject_Z (Z.of_nat (length b)))).\n\n"
        "Definition show (x : Q) : Z * positive := (Qnum (Qred x), Qden (Qred x)).\n\n"
        "Definition row (b : list (bool * Q)) : list (Z * positive) :=\n"
        "  let bins := seq 0 (length b) in\n"
        "  map show [D.vHat bins (cc b) (pp b); " + n_hat + "; D.nullity bins (pp b);\n"
        "            D.vBarPos bins (cc b) (pp b); D.vBarNeg bins (cc b) (pp b)].\n\n"
        "Open Scope Z_scope.\n"
        "Compute map row blocks.\n"
    )


PAIR = re.compile(r"\(\s*(-?\d+)(?:%Z)?\s*,\s*(\d+)(?:%positive)?\s*\)")


def lean_readings(text: str) -> list[list[Fraction]]:
    rows = [line.split() for line in text.split("\n") if line.strip()]
    return [[Fraction(field) for field in row] for row in rows]


def rocq_readings(text: str) -> list[list[Fraction]]:
    pairs = [Fraction(int(n), int(d)) for n, d in PAIR.findall(text)]
    width = len(READINGS)
    if len(pairs) % width != 0:
        raise SystemExit(f"compare_estimator_rocq: Rocq printed {len(pairs)} rationals, not a multiple of {width}")
    return [pairs[i : i + width] for i in range(0, len(pairs), width)]


def compare(lean_path: Path, rocq_path: Path, mutant_path: Path) -> int:
    lean = lean_readings(lean_path.read_text(encoding="utf-8"))
    rocq = rocq_readings(rocq_path.read_text(encoding="utf-8"))
    mutant = rocq_readings(mutant_path.read_text(encoding="utf-8"))
    if not (len(lean) == len(rocq) == len(mutant) == len(BLOCKS)):
        print(
            f"compare_estimator_rocq: {len(lean)} Lean, {len(rocq)} Rocq and {len(mutant)} mutant blocks, "
            f"expected {len(BLOCKS)}",
            file=sys.stderr,
        )
        return 1
    status = 0
    for index, (lrow, rrow) in enumerate(zip(lean, rocq, strict=True)):
        for name, lvalue, rvalue in zip(READINGS, lrow, rrow, strict=True):
            if lvalue != rvalue:
                print(f"compare_estimator_rocq: block {index} {name}: Lean {lvalue}, Rocq {rvalue}", file=sys.stderr)
                status = 1
    rejected = sum(1 for lrow, mrow in zip(lean, mutant, strict=True) if lrow != mrow)
    if rejected == 0:
        print("compare_estimator_rocq: the comparison accepted the unsigned-mean mutant", file=sys.stderr)
        status = 1
    if status == 0:
        print(
            f"compare_estimator_rocq: {len(lean)} blocks, {', '.join(READINGS)} agree exactly; "
            f"the unsigned-mean mutant differs on {rejected} block(s)"
        )
    return status


def main(arguments: list[str]) -> int:
    if len(arguments) == 4 and arguments[0] == "cases":
        all_blocks = blocks()
        Path(arguments[1]).write_text(lean_program(all_blocks), encoding="utf-8")
        Path(arguments[2]).write_text(rocq_program(all_blocks, False), encoding="utf-8")
        Path(arguments[3]).write_text(rocq_program(all_blocks, True), encoding="utf-8")
        return 0
    if len(arguments) == 4 and arguments[0] == "compare":
        return compare(Path(arguments[1]), Path(arguments[2]), Path(arguments[3]))
    print(
        "usage: compare_estimator_rocq.py cases LEAN_OUT ROCQ_OUT MUTANT_OUT"
        " | compare LEAN_OUTPUT ROCQ_OUTPUT MUTANT_OUTPUT",
        file=sys.stderr,
    )
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
