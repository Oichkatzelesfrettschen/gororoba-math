"""Cases and comparison for ci/compare_box_kite_census.sh: the sedenion sign table and associator signs.

Usage:

    "$PYTHON" -I -B ci/compare_box_kite_census.py cases ROCQ_FILE ROCQ_MUTANT_FILE
    "$PYTHON" -I -B ci/compare_box_kite_census.py compare QUANTUM ROCQ_OUTPUT

`cases` writes a Rocq file that evaluates, with vm_compute, the 256 entries sed_sign i j of
rocq/open/verified/C1467_XORSignCocycle.v (i, then j, below 16) and the 4096 pairs (lsign i j k,
rsign i j k) of rocq/open/verified/C1630_BasisAssociatorTensor.v (i, j, then k below 16), whose
product is that file's omega; and a mutated reference whose pairs take rsign with its first two
arguments exchanged.

`compare` evaluates gororoba_quantum/cd_core.py of the gororoba-quantum checkout QUANTUM on the same
inputs: cd_sign(16, i, j), and triple_sign(16, i, j, k), whose product is omega of
scripts/box_kite_census.py there. It exits 0 when every value agrees, 1 on the first difference, and 2
when an output is unreadable or incomplete or cd_core does not import."""

import re
import sys
from pathlib import Path

DIM = 16
EVAL = re.compile(r"^\s*=(.*?):\s*list", re.MULTILINE | re.DOTALL)
INTEGER = re.compile(r"-?\d+")

ROCQ_HEAD = """From Stdlib Require Import List ZArith.
From OpenGororobaVerified Require Import C1467_XORSignCocycle C1630_BasisAssociatorTensor.
Import ListNotations.

Definition idx : list nat := seq 0 16.
Definition sign_rows : list Z := flat_map (fun i => map (fun j => sed_sign i j) idx) idx.
"""

PAIRS = """Definition associator_pairs : list (Z * Z) :=
  flat_map (fun i => flat_map (fun j => map (fun k => ({left}, {right})) idx) idx) idx.

Eval vm_compute in sign_rows.
Eval vm_compute in associator_pairs.
"""


def write_cases(rocq_file: Path, mutant_file: Path) -> None:
    rocq_file.write_text(ROCQ_HEAD + "\n" + PAIRS.format(left="lsign i j k", right="rsign i j k"))
    mutant_file.write_text(ROCQ_HEAD + "\n" + PAIRS.format(left="lsign i j k", right="rsign j i k"))


def rocq_values(text: str) -> tuple[list[int], list[int]]:
    blocks = EVAL.findall(text)
    if len(blocks) != 2:
        raise ValueError(f"{len(blocks)} evaluations printed, not 2")
    signs = [int(v) for v in INTEGER.findall(blocks[0])]
    pairs = [int(v) for v in INTEGER.findall(blocks[1])]
    if len(signs) != DIM * DIM or len(pairs) != 2 * DIM**3:
        raise ValueError(f"{len(signs)} signs and {len(pairs)} pair values, not {DIM * DIM} and {2 * DIM**3}")
    return signs, pairs


def reference_values(quantum: Path) -> tuple[list[int], list[int]]:
    sys.path.insert(0, str(quantum / "gororoba_quantum"))
    import cd_core  # noqa: PLC0415

    signs = [cd_core.cd_sign(DIM, i, j) for i in range(DIM) for j in range(DIM)]
    pairs: list[int] = []
    for i in range(DIM):
        for j in range(DIM):
            for k in range(DIM):
                pairs.extend(cd_core.triple_sign(DIM, i, j, k))
    return signs, pairs


def compare(quantum: Path, rocq_output: Path) -> int:
    try:
        rocq_signs, rocq_pairs = rocq_values(rocq_output.read_text())
    except (OSError, ValueError) as error:
        print(f"compare_box_kite_census: Rocq output unreadable: {error}", file=sys.stderr)
        return 2
    try:
        ref_signs, ref_pairs = reference_values(quantum)
    except (ImportError, OSError) as error:
        print(f"compare_box_kite_census: cd_core does not import: {error}", file=sys.stderr)
        return 2
    for n, (a, b) in enumerate(zip(rocq_signs, ref_signs, strict=True)):
        if a != b:
            print(f"compare_box_kite_census: sed_sign {n // DIM} {n % DIM} = {a}, cd_sign = {b}", file=sys.stderr)
            return 1
    for n, (a, b) in enumerate(zip(rocq_pairs, ref_pairs, strict=True)):
        if a != b:
            t, side = divmod(n, 2)
            i, rest = divmod(t, DIM * DIM)
            j, k = divmod(rest, DIM)
            name = "rsign" if side else "lsign"
            print(f"compare_box_kite_census: {name} {i} {j} {k} = {a}, triple_sign gives {b}", file=sys.stderr)
            return 1
    omega_negative = sum(1 for t in range(DIM**3) if ref_pairs[2 * t] * ref_pairs[2 * t + 1] == -1)
    print(
        f"compare_box_kite_census: {DIM * DIM} signs and {DIM**3} associator sign pairs agree "
        f"({omega_negative} triples with omega = -1)"
    )
    return 0


def main(argv: list[str]) -> int:
    if len(argv) == 3 and argv[0] == "cases":
        write_cases(Path(argv[1]), Path(argv[2]))
        return 0
    if len(argv) == 3 and argv[0] == "compare":
        return compare(Path(argv[1]), Path(argv[2]))
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
