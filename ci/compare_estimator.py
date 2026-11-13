"""Inputs and comparison for ci/compare_estimator.sh.

`cases QUANTUM_DIR LEAN_OUT JSON_OUT` builds a fixed list of blocks without a
random draw, runs gororoba-quantum's `pathion_kernel_map._pair_summary` on
each, and writes (a) a Lean file that evaluates `KernelMap.vHat`,
`KernelMap.nHat` and `KernelMap.nullity` over the rationals on the same
observed contrasts and ideal signs, and (b) the Python readings as JSON.
Every bin of every block is decided (ideal contrast +1 or -1), the scope of
the Lean theorems. The observed contrast handed to Lean is the exact rational
value of each float of `pathion_kernel_map.output_contrast`, so both sides
read identical numbers.

`compare JSON_IN LEAN_OUTPUT` reads the three rationals Lean printed per
block and requires each to agree with the Python float within 1e-12 relative
to max(1, |value|). It then requires the same comparator to reject a mutated
reference, the estimate formed with an unsigned mean in place of the signed
visibility, on at least one block.

Exit status: 0 agreement and the mutant rejected, 1 a difference or an
accepted mutant, 2 a usage error.
"""

import json
import sys
from fractions import Fraction
from pathlib import Path

TOLERANCE = 1e-12
# (bins, indices of the bins with ideal contrast -1); an empty tuple is a
# block the estimator is forced to read as bins / 2.
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


def laws(case: int, bins: int, negative: tuple[int, ...]):
    """Ideal and observed laws of one block, as arrays of 2 * bins weights."""
    import numpy as np

    ideal_plus = np.zeros(2 * bins)
    ideal_minus = np.zeros(2 * bins)
    observed_plus = np.zeros(2 * bins)
    observed_minus = np.zeros(2 * bins)
    for y in range(bins):
        sign_negative = y in negative
        ideal_plus[y + (bins if sign_negative else 0)] = 1.0 / bins
        ideal_minus[y + (0 if sign_negative else bins)] = 1.0 / bins
        # Unnormalized observed weights: the ideal pattern with a
        # bin-dependent leak into the other selector value.
        leak_plus = 1 + (5 * y + 3 * case) % 7
        leak_minus = 1 + (3 * y + 5 * case + 2) % 9
        keep_plus = 11 + (2 * y + case) % 5
        keep_minus = 13 + (y + 2 * case) % 4
        observed_plus[y + (bins if sign_negative else 0)] = keep_plus
        observed_plus[y + (0 if sign_negative else bins)] = leak_plus
        observed_minus[y + (0 if sign_negative else bins)] = keep_minus
        observed_minus[y + (bins if sign_negative else 0)] = leak_minus
    observed_plus /= observed_plus.sum()
    observed_minus /= observed_minus.sum()
    return ideal_plus, ideal_minus, observed_plus, observed_minus


def rational_literal(value: Fraction) -> str:
    return f"(({value.numerator} : ℚ) / {value.denominator})"


def write_cases(quantum: Path, lean_out: Path, json_out: Path) -> None:
    sys.path.insert(0, str(quantum / "gororoba_quantum"))
    import numpy as np
    import pathion_kernel_map as kernel_map

    readings = []
    lean_blocks = []
    for case, (bins, negative) in enumerate(BLOCKS):
        ideal_plus, ideal_minus, observed_plus, observed_minus = laws(case, bins, negative)
        summary = kernel_map._pair_summary(
            "block",
            {"block_plus": observed_plus, "block_minus": observed_minus},
            {"block_plus": ideal_plus, "block_minus": ideal_minus},
        )
        observed = kernel_map.output_contrast(observed_plus, observed_minus)
        ideal = kernel_map.output_contrast(ideal_plus, ideal_minus)
        if not bool(np.all(np.abs(ideal) == 1.0)):
            raise SystemExit(f"compare_estimator: block {case} holds an undecided bin")
        unsigned = float(observed.sum() / 2.0) / float(np.mean(observed))
        readings.append(
            {
                "bins": bins,
                "v_hat": summary["block_visibility"],
                "n_hat": summary["block_nullity_estimate"],
                "nullity": summary["block_nullity_ideal"],
                "mutant_n_hat": unsigned,
            }
        )
        entries = ", ".join(
            f"({'true' if ideal[y] > 0 else 'false'}, {rational_literal(Fraction(float(observed[y])))})"
            for y in range(bins)
        )
        lean_blocks.append(f"  [{entries}]")
    lean_out.write_text(
        "import GororobaMath\n\nopen KernelMap\n\n"
        "def blocks : List (List (Bool × ℚ)) := [\n" + ",\n".join(lean_blocks) + "\n]\n\n"
        "def main : IO Unit := do\n"
        "  for block in blocks do\n"
        "    let bins := Finset.range block.length\n"
        "    let contrast : ℕ → ℚ := fun y => (block.getD y (false, 0)).2\n"
        "    let positive : ℕ → Prop := fun y => (block.getD y (false, 0)).1 = true\n"
        '    IO.println s!"{vHat bins contrast positive} {nHat bins contrast positive} '
        '{nullity (K := ℚ) bins positive}"\n',
        encoding="utf-8",
    )
    json_out.write_text(json.dumps(readings), encoding="utf-8")


def differs(lean_value: Fraction, python_value: float) -> bool:
    return abs(float(lean_value) - python_value) > TOLERANCE * max(1.0, abs(python_value))


def compare(json_in: Path, lean_output: Path) -> int:
    readings = json.loads(json_in.read_text(encoding="utf-8"))
    lines = lean_output.read_text(encoding="utf-8").split("\n")
    lines = [line for line in lines if line.strip()]
    if len(lines) != len(readings):
        print(f"compare_estimator: Lean printed {len(lines)} blocks, Python {len(readings)}", file=sys.stderr)
        return 1
    status = 0
    mutant_rejected = 0
    for index, (line, reading) in enumerate(zip(lines, readings, strict=True)):
        v_hat, n_hat, nullity = (Fraction(field) for field in line.split())
        for name, lean_value in (("v_hat", v_hat), ("n_hat", n_hat), ("nullity", nullity)):
            if differs(lean_value, reading[name]):
                print(
                    f"compare_estimator: block {index} {name}: Lean {float(lean_value)!r}, Python {reading[name]!r}",
                    file=sys.stderr,
                )
                status = 1
        if differs(n_hat, reading["mutant_n_hat"]):
            mutant_rejected += 1
    if mutant_rejected == 0:
        print("compare_estimator: the comparator accepted the unsigned-mean mutant on every block", file=sys.stderr)
        status = 1
    if status == 0:
        print(
            f"compare_estimator: {len(readings)} blocks, v_hat, n_hat and nullity agree within {TOLERANCE:g}; "
            f"the unsigned-mean mutant differs on {mutant_rejected} block(s)"
        )
    return status


def main(arguments: list[str]) -> int:
    if len(arguments) == 4 and arguments[0] == "cases":
        write_cases(Path(arguments[1]), Path(arguments[2]), Path(arguments[3]))
        return 0
    if len(arguments) == 3 and arguments[0] == "compare":
        return compare(Path(arguments[1]), Path(arguments[2]))
    print(
        "usage: compare_estimator.py cases QUANTUM_DIR LEAN_OUT JSON_OUT | compare JSON_IN LEAN_OUTPUT",
        file=sys.stderr,
    )
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
