"""Inputs and comparison for ci/compare_kernel_map_bins.sh.

`cases QUANTUM_DIR LEAN_OUT JSON_OUT` computes, with gororoba-quantum's
`pathion_kernel_map`, the ideal output contrast c(y) = P_plus(s = 0 | y) -
P_minus(s = 0 | y) of the kernel map of every operand of `OPERANDS` and of
both quarter-turn twins of `TWINS`, from the ideal laws of
`kernel_map_circuit(operand, plus)` and `output_contrast`. Output bin y is
read as the algebra index y (bit b of y on qubit b, the convention of the
module). It writes (a) a Lean file that, for each case, takes the bins with
c(y) = +1 as `pos` and evaluates the bin contract of
`KernelMap.nullity_eq_alignedPairCount` against `Tower.misaligned 5 i j`
(every index of an aligned pair is a +1 bin; a misaligned pair holds one
+1 bin and one -1 bin), `Tower.alignedPairCount 5 i j` and
`KernelMap.nullity` over the rationals on the 32 bins, and (b) the Python
readings as JSON: whether every bin is decided (|c| = 1) and half the sum of
c. A twin e_i - e_j is evaluated against the alignment of e_i + e_j, whose
aligned pairs are the same (`Tower.kerEquivAddSub`).

Two mutated references enter as cases that must be rejected: the member
`kmap_flip3_e1pe18` (one SELECT sign negated, `flip_input`), and the
contrast of e_1 + e_18 with the bin 0 negated.

`compare JSON_IN LEAN_OUTPUT` accepts a case when every bin is decided, the
contract holds in Lean, and `alignedPairCount`, `nullity` and the Python
half-sum agree. It requires every operand and twin to be accepted and every
mutant to be rejected.

Exit status: 0 every operand accepted and every mutant rejected, 1
otherwise, 2 a usage error.
"""

import json
import sys
from fractions import Fraction
from pathlib import Path

DIM = 32
NEGATED_BIN = 0


def write_cases(quantum: Path, lean_out: Path, json_out: Path) -> None:
    sys.path.insert(0, str(quantum / "gororoba_quantum"))
    import numpy as np
    import pathion_kernel_map as kernel_map

    def contrast(operand: tuple[int, int, int], **options: int) -> np.ndarray:
        plus = kernel_map.ideal_law(kernel_map.kernel_map_circuit(operand, True, **options))
        minus = kernel_map.ideal_law(kernel_map.kernel_map_circuit(operand, False, **options))
        return kernel_map.output_contrast(plus, minus)

    cases = []
    for operand in (*kernel_map.OPERANDS, *(twin for twin, _primary in kernel_map.TWINS)):
        cases.append((f"kmap_{kernel_map.operand_tag(operand)}", operand, contrast(operand), False))
    flip = kernel_map.FLIP_OPERAND
    flip_name = f"kmap_flip{kernel_map.FLIP_INPUT}_{kernel_map.operand_tag(flip)}"
    cases.append((flip_name, flip, contrast(flip, flip_input=kernel_map.FLIP_INPUT), True))
    negated = contrast(flip).copy()
    negated[NEGATED_BIN] = -negated[NEGATED_BIN]
    cases.append((f"negated_bin{NEGATED_BIN}_{kernel_map.operand_tag(flip)}", flip, negated, True))

    readings = []
    lean_cases = []
    for name, (i, j, _t), c, mutant in cases:
        if c.size != DIM:
            raise SystemExit(f"compare_kernel_map_bins: {name} has {c.size} bins, expected {DIM}")
        decided = bool(np.all(np.abs(np.abs(c) - 1.0) <= 1e-9))
        readings.append(
            {
                "name": name,
                "mutant": mutant,
                "decided": decided,
                "half_sum": str(Fraction(round(float(c.sum()) * 64), 128)),
            }
        )
        bins = ", ".join("true" if value > 0 else "false" for value in c)
        lean_cases.append(f'  ("{name}", {i}, {j}, [{bins}])')
    lean_out.write_text(
        "import GororobaMath\n\nopen CayleyDickson.Tower KernelMap\n\n"
        "def cases : List (String × ℕ × ℕ × List Bool) := [\n" + ",\n".join(lean_cases) + "\n]\n\n"
        "def main : IO Unit := do\n"
        "  for (name, i, j, bins) in cases do\n"
        "    let a := BitVec.ofNat 5 i\n"
        "    let b := BitVec.ofNat 5 j\n"
        "    let positive : ℕ → Bool := fun y => bins.getD y false\n"
        "    let contract := (List.range 32).all fun y =>\n"
        "      let x := BitVec.ofNat 5 y\n"
        "      if misaligned 5 a b x then positive (partner a b x).toNat != positive y else positive y\n"
        "    let exact := nullity (K := ℚ) (Finset.range 32) fun y => positive y = true\n"
        '    IO.println s!"{name} {contract} {alignedPairCount 5 a b} {exact}"\n',
        encoding="utf-8",
    )
    json_out.write_text(json.dumps(readings), encoding="utf-8")


def accepted(reading: dict, contract: str, count: str, exact: str) -> bool:
    half_sum = Fraction(reading["half_sum"])
    return reading["decided"] and contract == "true" and Fraction(count) == half_sum and Fraction(exact) == half_sum


def compare(json_in: Path, lean_output: Path) -> int:
    readings = json.loads(json_in.read_text(encoding="utf-8"))
    lines = [line for line in lean_output.read_text(encoding="utf-8").split("\n") if line.strip()]
    if len(lines) != len(readings):
        print(f"compare_kernel_map_bins: Lean printed {len(lines)} cases, Python {len(readings)}", file=sys.stderr)
        return 1
    status = 0
    operands = 0
    mutants = 0
    for line, reading in zip(lines, readings, strict=True):
        name, contract, count, exact = line.split()
        if name != reading["name"]:
            print(f"compare_kernel_map_bins: Lean case {name}, Python case {reading['name']}", file=sys.stderr)
            return 1
        verdict = accepted(reading, contract, count, exact)
        detail = (
            f"decided {reading['decided']}, contract {contract}, alignedPairCount {count}, "
            f"nullity {exact}, half-sum {reading['half_sum']}"
        )
        if reading["mutant"]:
            mutants += 1
            if verdict:
                print(f"compare_kernel_map_bins: mutant {name} accepted ({detail})", file=sys.stderr)
                status = 1
        else:
            operands += 1
            if not verdict:
                print(f"compare_kernel_map_bins: {name} rejected ({detail})", file=sys.stderr)
                status = 1
    if mutants == 0:
        print("compare_kernel_map_bins: no mutated reference was evaluated", file=sys.stderr)
        status = 1
    if status == 0:
        print(
            f"compare_kernel_map_bins: {operands} operands meet the bin contract with "
            f"alignedPairCount = nullity = half-sum; {mutants} mutated references rejected"
        )
    return status


def main(arguments: list[str]) -> int:
    if len(arguments) == 4 and arguments[0] == "cases":
        write_cases(Path(arguments[1]), Path(arguments[2]), Path(arguments[3]))
        return 0
    if len(arguments) == 3 and arguments[0] == "compare":
        return compare(Path(arguments[1]), Path(arguments[2]))
    print(
        "usage: compare_kernel_map_bins.py cases QUANTUM_DIR LEAN_OUT JSON_OUT | compare JSON_IN LEAN_OUTPUT",
        file=sys.stderr,
    )
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
