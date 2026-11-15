"""Inputs and comparison for ci/compare_kernel_map_bins.sh.

`cases LEVEL SCOPE QUANTUM_DIR LEAN_OUT DATA_OUT JSON_OUT` computes, with
gororoba-quantum's `pathion_kernel_map` at dimension D = 2^LEVEL, the ideal
output contrast c(y) = P_plus(s = 0 | y) - P_minus(s = 0 | y) of the kernel
map of every two-term operand e_i + t e_j with i != j and t = +1 or -1, from
the ideal laws of `kernel_map_circuit(operand, plus, dim=D)` and
`output_contrast`. Output bin y is read as the algebra index y (bit b of y on
qubit b, the convention of the module). At LEVEL 5 the six operands of
`OPERANDS` and the two of `TWINS` are among them. At the levels of
`pathion_wide_coset.WIDE_OPERANDS` (6 and 7) the cases also hold each wide
operand as the hardware runs it: the coset blocks of
`pathion_coset_block.block_circuit` with the module's `default_basis`, each
block contrast placed at the algebra indices `output_labels` names. SCOPE
`all` takes every operand; SCOPE `wide` (levels 6 and 7) takes only the wide
operands and the mutants, the circuits the 64- and 128-dimensional runs
executed.

It writes (a) a Lean program that reads the data file and evaluates, with the
bins of c(y) = +1 as `pos` (bit y of a mask), `KernelMap.binContract`,
`Tower.alignedPairCount` and `KernelMap.nullity` over the rationals on the
D bins `BitVec LEVEL`, (b) the data file, one case per line, and (c) the
Python readings as JSON: whether every bin is decided (|c| = 1) and half the
sum of c. `binContract` is the hypothesis of
`KernelMap.nullity_eq_alignedPairCount_of_binContract`, so a case whose
contract evaluates to true has exact nullity `alignedPairCount` by that
theorem; the nullity column cross-checks it by direct evaluation. A twin
e_i - e_j is evaluated against the alignment of e_i + e_j, whose aligned
pairs are the same (`Tower.kerEquivAddSub`).

Mutated references must be rejected by the contract itself, at every level:
the operand e_1 + e_18 with one SELECT sign negated (`flip_input` 3, the
member `kmap_flip3_e1pe18` at LEVEL 5), the contrast of e_1 + e_18 with the
bin 0 negated, and at LEVEL 6 and 7 the cocycle-free wide operand
(`m64`, `m128`). Each must have every bin decided, `binContract` false and
a nullity that differs from `alignedPairCount`.

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

FLIP_OPERAND = (1, 18, 1)
FLIP_INPUT = 3
NEGATED_BIN = 0

LEAN_PROGRAM = """import GororobaMath

open CayleyDickson.Tower KernelMap

def level : ℕ := {level}

def main (arguments : List String) : IO Unit := do
  let path ← match arguments with
    | [path] => pure path
    | _ => throw (IO.userError "usage: DATA_FILE")
  for line in ← IO.FS.lines path do
    match line.splitOn " " with
    | [name, i, j, mask] =>
      let a := BitVec.ofNat level i.toNat!
      let b := BitVec.ofNat level j.toNat!
      let bits := mask.toNat!
      let pos : BitVec level → Bool := fun x => bits.testBit x.toNat
      let exact := nullity (K := ℚ) Finset.univ fun x => pos x = true
      IO.println s!"{{name}} {{binContract level a b pos}} {{alignedPairCount level a b}} {{exact}}"
    | _ => throw (IO.userError s!"malformed case line: {{line}}")
"""


def write_cases(level: int, scope: str, quantum: Path, lean_out: Path, data_out: Path, json_out: Path) -> None:
    sys.path.insert(0, str(quantum / "gororoba_quantum"))
    import numpy as np
    import pathion_coset_block as coset_block
    import pathion_kernel_map as kernel_map
    import pathion_wide_coset as wide_coset

    dim = 1 << level

    def contrast(operand: tuple[int, int, int], **options: int) -> np.ndarray:
        plus = kernel_map.ideal_law(kernel_map.kernel_map_circuit(operand, True, dim=dim, **options))
        minus = kernel_map.ideal_law(kernel_map.kernel_map_circuit(operand, False, dim=dim, **options))
        return kernel_map.output_contrast(plus, minus)

    def tiled_contrast(wide: "wide_coset.WideOperand") -> np.ndarray:
        options = {"cocycle_free": True} if wide.cocycle_free else {}
        full = np.full(dim, np.nan)
        for block in wide.blocks():
            plus = coset_block.block_law(coset_block.block_circuit(block, True, **options))
            minus = coset_block.block_law(coset_block.block_circuit(block, False, **options))
            for y, label in enumerate(coset_block.output_labels(block)):
                full[label] = coset_block.output_contrast(plus, minus)[y]
        if np.isnan(full).any():
            raise SystemExit(f"compare_kernel_map_bins: the blocks of {wide.key} leave a bin uncovered")
        return full

    members: dict[tuple[int, int, int], str] = {}
    if level == 5:
        members = {operand: f"kmap_{kernel_map.operand_tag(operand)}" for operand in kernel_map.OPERANDS}
        members |= {twin: f"kmap_twin_{kernel_map.operand_tag(twin)}" for twin, _primary in kernel_map.TWINS}
    operands = [(i, j, t) for i in range(dim) for j in range(dim) if i != j for t in (1, -1)] if scope == "all" else []
    cases = [
        (members.get(operand, kernel_map.operand_tag(operand)), operand, contrast(operand), False, operand in members)
        for operand in operands
    ]
    for wide in wide_coset.WIDE_OPERANDS:
        if wide.dim == dim:
            name = f"wide_{wide.key}_{kernel_map.operand_tag(wide.operand)}"
            cases.append((name, wide.operand, tiled_contrast(wide), wide.cocycle_free, not wide.cocycle_free))
    flip_tag = kernel_map.operand_tag(FLIP_OPERAND)
    flip_name = f"kmap_flip{FLIP_INPUT}_{flip_tag}" if level == 5 else f"flip{FLIP_INPUT}_{flip_tag}"
    cases.append((flip_name, FLIP_OPERAND, contrast(FLIP_OPERAND, flip_input=FLIP_INPUT), True, False))
    negated = contrast(FLIP_OPERAND).copy()
    negated[NEGATED_BIN] = -negated[NEGATED_BIN]
    cases.append((f"negated_bin{NEGATED_BIN}_{flip_tag}", FLIP_OPERAND, negated, True, False))

    readings = []
    lines = []
    for name, (i, j, _t), c, mutant, member in cases:
        if c.size != dim:
            raise SystemExit(f"compare_kernel_map_bins: {name} has {c.size} bins, expected {dim}")
        readings.append(
            {
                "name": name,
                "member": member,
                "mutant": mutant,
                "decided": bool(np.all(np.abs(np.abs(c) - 1.0) <= 1e-9)),
                "half_sum": str(Fraction(round(float(c.sum()) * 64), 128)),
            }
        )
        mask = sum(1 << y for y in range(dim) if c[y] > 0)
        lines.append(f"{name} {i} {j} {mask}")
    lean_out.write_text(LEAN_PROGRAM.format(level=level), encoding="utf-8")
    data_out.write_text("\n".join(lines) + "\n", encoding="utf-8")
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
    if mutants < 2:
        print(f"compare_kernel_map_bins: {mutants} mutated references evaluated, expected at least 2", file=sys.stderr)
        status = 1
    if status == 0:
        print(
            f"compare_kernel_map_bins: {operands} cases ({members} named members) meet the bin contract "
            f"with alignedPairCount = nullity = half-sum; {mutants} mutated references rejected by the contract"
        )
    return status


def main(arguments: list[str]) -> int:
    scopes = {"5": ("all",), "6": ("all", "wide"), "7": ("all", "wide")}
    if len(arguments) == 7 and arguments[0] == "cases" and arguments[2] in scopes.get(arguments[1], ()):
        level, scope = int(arguments[1]), arguments[2]
        write_cases(level, scope, Path(arguments[3]), Path(arguments[4]), Path(arguments[5]), Path(arguments[6]))
        return 0
    if len(arguments) == 3 and arguments[0] == "compare":
        return compare(Path(arguments[1]), Path(arguments[2]))
    print(
        "usage: compare_kernel_map_bins.py cases LEVEL SCOPE QUANTUM_DIR LEAN_OUT DATA_OUT JSON_OUT | "
        "compare JSON_IN LEAN_OUTPUT (LEVEL 5 with SCOPE all; LEVEL 6 or 7 with SCOPE all or wide)",
        file=sys.stderr,
    )
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
