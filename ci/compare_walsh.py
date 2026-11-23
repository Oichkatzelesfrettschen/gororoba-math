"""Cases and comparison of ci/compare_walsh.sh.

`cases QUANTUM LEAN_OUT PY_OUT` reads the functions `walsh_matrix` and `coefficients` from
docs/evidence/pathion-kernel-map/nhat-bias/nhat_spectral.py of the gororoba-quantum checkout QUANTUM (their source
alone, so the packages the rest of that module imports are not needed), evaluates them on 8 bins, and writes the
Lean program that evaluates `KernelMap.walshChar` and `KernelMap.coeff` on the same inputs over the rationals.
`compare PY_OUT LEAN_TXT` requires the two outputs to be equal as exact fractions. `mutate PY_OUT MUTANT_OUT`
negates one entry of the reference, which `compare` must then reject.
"""

from __future__ import annotations

import ast
import json
import sys
from fractions import Fraction
from pathlib import Path

D = 3
CONTRASTS = [
    [1, 1, 1, 1, 1, 1, 1, 1],
    [1, -1, 1, -1, -1, 1, -1, 1],
    [3, 0, -2, 5, 1, 1, -4, 7],
    [1, 1, 1, 1, -1, -1, -1, 1],
]
MODULE = "docs/evidence/pathion-kernel-map/nhat-bias/nhat_spectral.py"


def reference(quantum: Path) -> dict[str, list[str]]:
    import numpy as np

    tree = ast.parse((quantum / MODULE).read_text())
    names = {"walsh_matrix", "coefficients"}
    wanted = [node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name in names]
    if len(wanted) != 2:
        raise SystemExit(f"compare_walsh: {MODULE} does not define walsh_matrix and coefficients")

    def expect(condition: bool, message: str) -> None:
        if not condition:
            raise SystemExit(f"compare_walsh: {message}")

    scope: dict[str, object] = {"np": np, "expect": expect}
    exec(compile(ast.Module(body=wanted, type_ignores=[]), MODULE, "exec"), scope)  # noqa: S102 - two named functions
    n = 2**D
    matrix = scope["walsh_matrix"](n)  # type: ignore[operator]
    chars = [str(Fraction(float(matrix[a][y])).limit_denominator(1)) for a in range(n) for y in range(n)]
    coeffs = []
    for contrast in CONTRASTS:
        values = scope["coefficients"](np.array(contrast, dtype=float))  # type: ignore[operator]
        coeffs += [str(Fraction(float(v)).limit_denominator(n)) for v in values]
    return {"chars": chars, "coeffs": coeffs}


def lean_program() -> str:
    rows = ", ".join("[" + ", ".join(str(v) for v in c) + "]" for c in CONTRASTS)
    return f"""import GororobaMath.KernelMap.EstimatorWalsh
open KernelMap

def bits (n : Nat) : Fin {D} → Bool := fun i => n.testBit i.val

def index (y : Fin {D} → Bool) : Nat := (List.finRange {D}).foldl (fun acc i => acc + if y i then 2 ^ i.val else 0) 0

def contrasts : List (List ℚ) := [{rows}]

def main : IO Unit := do
  for a in List.range {2**D} do
    for y in List.range {2**D} do
      IO.println s!"char {{walshChar ℚ {D} (bits a) (bits y)}}"
  for c in contrasts do
    for a in List.range {2**D} do
      let f : (Fin {D} → Bool) → ℚ := fun y => c.getD (index y) 0
      IO.println s!"coeff {{coeff (Finset.univ : Finset (Fin {D} → Bool)) (walshChar ℚ {D}) f (bits a)}}"
"""


def compare(py_out: Path, lean_txt: Path) -> int:
    ref = json.loads(py_out.read_text())
    lines = [line.split() for line in lean_txt.read_text().splitlines() if line.strip()]
    chars = [Fraction(value) for kind, value in lines if kind == "char"]
    coeffs = [Fraction(value) for kind, value in lines if kind == "coeff"]
    if chars != [Fraction(v) for v in ref["chars"]] or coeffs != [Fraction(v) for v in ref["coeffs"]]:
        print("compare_walsh: the Lean values differ from the reference", file=sys.stderr)
        return 1
    print(f"compare_walsh: {len(chars)} character values and {len(coeffs)} coefficients agree exactly")
    return 0


def main(argv: list[str]) -> int:
    if argv[1] == "cases":
        Path(argv[3]).write_text(lean_program())
        Path(argv[4]).write_text(json.dumps(reference(Path(argv[2]))))
        return 0
    if argv[1] == "compare":
        return compare(Path(argv[2]), Path(argv[3]))
    if argv[1] == "mutate":
        ref = json.loads(Path(argv[2]).read_text())
        ref["chars"][9] = str(-Fraction(ref["chars"][9]))
        Path(argv[3]).write_text(json.dumps(ref))
        return 0
    raise SystemExit("usage: compare_walsh.py cases QUANTUM LEAN PY | compare PY LEAN_TXT | mutate PY OUT")


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
