"""Cases and comparison for ci/compare_cz_matrix.sh: the entries of `Tower.czMatrix` against `_c_matrix`.

Usage:

    "$PYTHON" -I ci/compare_cz_matrix.py cases LEAN_FILE
    "$PYTHON" -I ci/compare_cz_matrix.py reference QUANTUM_CHECKOUT OUT_FILE [mutate]
    "$PYTHON" -I ci/compare_cz_matrix.py compare LEAN_OUTPUT REFERENCE_OUTPUT

`cases` draws integer vectors z of 2^k - 1 coordinates (the coordinates of a pure element at the
nonzero indices) at levels 4 and 5 from a fixed seed, every entry nonzero, and writes a Lean program
that prints the matrix of `GororobaMath.CayleyDickson.Tower.czMatrix_apply`: the entry at (r, c) is
`sign k (r ^^^ c) c * z_(r ^^^ c)`, with the term at `r ^^^ c = 0` equal to 0 (the coordinate of a
pure element at index 0). `czMatrix` itself is noncomputable, so the program evaluates the entry
formula that `czMatrix_apply` proves equal to it.

`reference` prints the same matrices from gororoba-quantum: at level 4 from `_c_matrix` of
`docs/evidence/a5-kernel-attachments/holomorphic_kernel_lemma.py` on real Gaussian integers, and at
level 5 from the same formula with `cd_sign(32, ...)` of `cd_core.py`, since `_c_matrix` is fixed at
level 4. `mutate` negates `cd_sign` at the index pair (3, 5) for both sizes, which every case
reaches. The module imports `flint` at the top and uses it in no function that `reference` calls, so
a stub module stands in when `flint` is absent.

`compare` exits 0 when both files hold the same matrices, 1 on the first differing line, and 2 when
a file is unreadable or the counts disagree.
"""

import importlib.util
import random
import sys
import types
from fractions import Fraction
from pathlib import Path

LEVELS = (4, 5)
PER_LEVEL = 4
SEED = 20261124
MUTATED_PAIR = (3, 5)
LEMMA = Path("docs/evidence/a5-kernel-attachments/holomorphic_kernel_lemma.py")


def draw() -> list[tuple[int, list[int]]]:
    """Returns the level and the 2^k - 1 coordinates of each case, every coordinate nonzero."""
    rng = random.Random(SEED)  # noqa: S311 - reproducible test vectors, not secrets
    out = []
    for k in LEVELS:
        for _ in range(PER_LEVEL):
            out.append((k, [rng.choice((-1, 1)) * rng.randint(1, 9) for _ in range(2**k - 1)]))
    return out


def write_cases(lean_file: Path) -> None:
    lines = [
        "import GororobaMath.CayleyDickson.CzMatrix",
        "",
        "open CayleyDickson Tower",
        "",
        "/-- The entry formula of `czMatrix_apply` for a pure element with the given coordinates. -/",
        "def czEntry (k : Nat) (z : List Int) (r c : BitVec k) : Int :=",
        "  let q := r ^^^ c",
        "  sign k q c * (if q = 0#k then 0 else z.getD (q.toNat - 1) 0)",
        "",
        "def printCz (k : Nat) (z : List Int) : IO Unit := do",
        "  for r in List.range (2 ^ k - 1) do",
        "    IO.println (String.intercalate \" \" ((List.range (2 ^ k - 1)).map fun c =>",
        "      toString (czEntry k z (BitVec.ofNat k (r + 1)) (BitVec.ofNat k (c + 1)))))",
        "",
        "def main : IO Unit := do",
    ]
    for k, z in draw():
        lines.append(f"  printCz {k} [{', '.join(str(v) for v in z)}]")
    lean_file.write_text("\n".join(lines) + "\n", encoding="utf-8")


def load_lemma(checkout: Path, mutate: bool) -> types.ModuleType:
    sys.modules.setdefault("flint", types.ModuleType("flint"))
    sys.path.insert(0, str(checkout / "gororoba_quantum"))
    spec = importlib.util.spec_from_file_location("holomorphic_kernel_lemma", checkout / LEMMA)
    if spec is None or spec.loader is None:
        raise OSError(f"cannot load {checkout / LEMMA}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    if mutate:
        original = module.cd_sign

        def mutated(size: int, p: int, q: int) -> int:
            sign = original(size, p, q)
            return -sign if (p, q) == MUTATED_PAIR else sign

        module.cd_sign = mutated
    return module


def write_reference(checkout: Path, out_file: Path, mutate: bool) -> None:
    module = load_lemma(checkout, mutate)
    lines = []
    for k, z in draw():
        size = 2**k
        if k == 4:
            gaussian = tuple((Fraction(v), Fraction(0)) for v in z)
            matrix = module._c_matrix(gaussian)  # noqa: SLF001 - the function under comparison
            for row in matrix:
                if any(imag != 0 for _, imag in row):
                    raise ValueError("an entry has an imaginary part")
                lines.append(" ".join(str(int(real)) for real, _ in row))
        else:
            for r in range(1, size):
                lines.append(
                    " ".join(
                        str(0 if r ^ c == 0 else module.cd_sign(size, r ^ c, c) * z[(r ^ c) - 1])
                        for c in range(1, size)
                    )
                )
    out_file.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    if len(sys.argv) == 3 and sys.argv[1] == "cases":
        write_cases(Path(sys.argv[2]))
        return 0
    if len(sys.argv) in (4, 5) and sys.argv[1] == "reference":
        try:
            write_reference(Path(sys.argv[2]), Path(sys.argv[3]), len(sys.argv) == 5 and sys.argv[4] == "mutate")
        except (OSError, ValueError, AttributeError, ImportError) as error:
            print(f"compare_cz_matrix: {error}", file=sys.stderr)
            return 2
        return 0
    if len(sys.argv) == 4 and sys.argv[1] == "compare":
        try:
            lean = Path(sys.argv[2]).read_text(encoding="utf-8").splitlines()
            ref = Path(sys.argv[3]).read_text(encoding="utf-8").splitlines()
        except OSError as error:
            print(f"compare_cz_matrix: {error}", file=sys.stderr)
            return 2
        expected = PER_LEVEL * sum(2**k - 1 for k in LEVELS)
        if len(lean) != expected or len(ref) != expected:
            print(
                f"compare_cz_matrix: expected {expected} rows, Lean printed {len(lean)}, reference {len(ref)}",
                file=sys.stderr,
            )
            return 2
        for index, (a, b) in enumerate(zip(lean, ref, strict=True)):
            if a != b:
                print(f"compare_cz_matrix: row {index} differs", file=sys.stderr)
                return 1
        print(f"compare_cz_matrix: {expected} rows agree")
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
