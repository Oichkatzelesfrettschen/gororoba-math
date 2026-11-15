"""Inputs and comparison for ci/compare_kernel_map_bins.sh.

`cases QUANTUM_DIR LEAN_OUT JSON_OUT` computes, with gororoba-quantum's
`pathion_kernel_map`, the ideal output contrast c(y) = P_plus(s = 0 | y) -
P_minus(s = 0 | y) of the kernel map of every two-term operand e_i + t e_j of
A_5 with i != j and t = +1 or -1 (1,984 operands, the six of `OPERANDS` and
the two of `TWINS` among them), from the ideal laws of
`kernel_map_circuit(operand, plus)` and `output_contrast`. Output bin y is
read as the algebra index y (bit b of y on qubit b, the convention of the
module). It writes (a) a Lean file that evaluates, with the bins of c(y) = +1
as `pos` (bit y of a mask), `KernelMap.binContract 5 i j pos`, `Tower.alignedPairCount 5 i j`
and `KernelMap.nullity` over the rationals on the 32 bins `BitVec 5`, and
(b) the Python readings as JSON: whether every bin is decided (|c| = 1) and
half the sum of c. `binContract` is the hypothesis of
`KernelMap.nullity_eq_alignedPairCount_of_binContract`, so an operand whose
contract evaluates to true has exact nullity `alignedPairCount` by that
theorem; the nullity column cross-checks it by direct evaluation. A twin
e_i - e_j is evaluated against the alignment of e_i + e_j, whose aligned
pairs are the same (`Tower.kerEquivAddSub`).

Two mutated references must be rejected by the contract itself: the member
`kmap_flip3_e1pe18` (one SELECT sign negated, `flip_input`), and the
contrast of e_1 + e_18 with the bin 0 negated. Each must have every bin
decided, `binContract` false, and a nullity that differs from
`alignedPairCount`.

`compare JSON_IN LEAN_OUTPUT` accepts an operand when every bin is decided,
the contract is true in Lean, and `alignedPairCount`, `nullity` and the
Python half-sum agree; it requires every operand accepted and every mutant
rejected as stated above.

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

    members = {operand: f"kmap_{kernel_map.operand_tag(operand)}" for operand in kernel_map.OPERANDS}
    members |= {twin: f"kmap_twin_{kernel_map.operand_tag(twin)}" for twin, _primary in kernel_map.TWINS}
    operands = [(i, j, t) for i in range(DIM) for j in range(DIM) if i != j for t in (1, -1)]
    if not set(members) <= set(operands):
        raise SystemExit("compare_kernel_map_bins: a kernel-map member lies outside the operand sweep")
    cases = [
        (members.get(operand, kernel_map.operand_tag(operand)), operand, contrast(operand), False)
        for operand in operands
    ]
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
        readings.append(
            {
                "name": name,
                "member": name.startswith("kmap_"),
                "mutant": mutant,
                "decided": bool(np.all(np.abs(np.abs(c) - 1.0) <= 1e-9)),
                "half_sum": str(Fraction(round(float(c.sum()) * 64), 128)),
            }
        )
        mask = sum(1 << y for y in range(DIM) if c[y] > 0)
        lean_cases.append(f'  ("{name}", {i}, {j}, {mask})')
    lean_out.write_text(
        "import GororobaMath\n\nopen CayleyDickson.Tower KernelMap\n\n"
        "set_option maxRecDepth 100000 in\n"
        "def cases : List (String × ℕ × ℕ × ℕ) := [\n" + ",\n".join(lean_cases) + "\n]\n\n"
        "def main : IO Unit := do\n"
        "  for (name, i, j, mask) in cases do\n"
        "    let a := BitVec.ofNat 5 i\n"
        "    let b := BitVec.ofNat 5 j\n"
        "    let pos : BitVec 5 → Bool := fun x => mask.testBit x.toNat\n"
        "    let exact := nullity (K := ℚ) Finset.univ fun x => pos x = true\n"
        '    IO.println s!"{name} {binContract 5 a b pos} {alignedPairCount 5 a b} {exact}"\n',
        encoding="utf-8",
    )
    json_out.write_text(json.dumps(readings), encoding="utf-8")


def compare(json_in: Path, lean_output: Path) -> int:
    readings = json.loads(json_in.read_text(encoding="utf-8"))
    lines = [line for line in lean_output.read_text(encoding="utf-8").split("\n") if line.strip()]
    if len(lines) != len(readings):
        print(f"compare_kernel_map_bins: Lean printed {len(lines)} cases, Python {len(readings)}", file=sys.stderr)
        return 1
    status = 0
    operands = members = mutants = 0
    for line, reading in zip(lines, readings, strict=True):
        name, contract, count, exact = line.split()
        if name != reading["name"]:
            print(f"compare_kernel_map_bins: Lean case {name}, Python case {reading['name']}", file=sys.stderr)
            return 1
        half_sum = Fraction(reading["half_sum"])
        detail = (
            f"decided {reading['decided']}, binContract {contract}, alignedPairCount {count}, "
            f"nullity {exact}, half-sum {half_sum}"
        )
        if reading["mutant"]:
            mutants += 1
            rejected = reading["decided"] and contract == "false" and Fraction(exact) != Fraction(count)
            if not rejected:
                print(
                    f"compare_kernel_map_bins: mutant {name} not rejected by the contract ({detail})", file=sys.stderr
                )
                status = 1
            else:
                print(f"compare_kernel_map_bins: mutant {name} rejected ({detail})")
            continue
        operands += 1
        members += reading["member"]
        agrees = Fraction(count) == half_sum and Fraction(exact) == half_sum
        if not (reading["decided"] and contract == "true" and agrees):
            print(f"compare_kernel_map_bins: {name} rejected ({detail})", file=sys.stderr)
            status = 1
        elif reading["member"]:
            print(f"compare_kernel_map_bins: {name} ({detail})")
    if mutants != 2:
        print(f"compare_kernel_map_bins: {mutants} mutated references evaluated, expected 2", file=sys.stderr)
        status = 1
    if status == 0:
        print(
            f"compare_kernel_map_bins: {operands} operands ({members} kernel-map members) meet the bin contract "
            f"with alignedPairCount = nullity = half-sum; {mutants} mutated references rejected by the contract"
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
