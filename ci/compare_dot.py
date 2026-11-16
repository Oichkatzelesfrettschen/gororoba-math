"""Cases and comparison for ci/compare_dot.sh: the Lean and Rocq trace form and real part.

Usage:

    "$PYTHON" -I ci/compare_dot.py cases LEAN_FILE ROCQ_FILE ROCQ_MUTANT_FILE
    "$PYTHON" -I ci/compare_dot.py compare LEAN_OUTPUT ROCQ_OUTPUT

`cases` draws 36 pairs of integer vectors, six at each level 0 to 5, from a
fixed seed, and writes a Lean program that prints `Tower.dot` and `Tower.re`
of each (GororobaMath.CayleyDickson.AnnihilatorSymmetry), a Rocq file that
evaluates `dot` and `re` of rocq/quantum/CdImaginarySumConference.v on the
same vectors with vm_compute, and a mutated Rocq reference whose dot keeps only
the first half of each pair and whose re reads the second half. A vector of
level k lists its 2^k coordinates with the first half of each pair first, the
order of both trees.

`compare` reads the integers each side printed, in order (the Lean program
prints one per line; Rocq prints each Eval as a line "= VALUE"), and exits 0
when both lists are equal and nonempty, 1 on the first difference, and 2 when
an output is unreadable.
"""

import random
import re
import sys
from pathlib import Path

LEVELS = range(6)
PER_LEVEL = 6
SEED = 20261116
EVAL = re.compile(r"^\s*= (-?[0-9]+)\s*$")


def draw() -> list[tuple[int, list[int], list[int]]]:
    """Returns the level and the two coordinate lists of each case."""
    rng = random.Random(SEED)  # noqa: S311 - reproducible test vectors, not secrets
    out = []
    for k in LEVELS:
        for _ in range(PER_LEVEL):
            size = 2**k
            x = [rng.randint(-9, 9) for _ in range(size)]
            y = [rng.randint(-9, 9) for _ in range(size)]
            out.append((k, x, y))
    return out


def lean_list(values: list[int]) -> str:
    return "[" + ", ".join(str(v) for v in values) + "]"


def rocq_list(values: list[int]) -> str:
    return "[" + "; ".join(f"({v})" for v in values) + "]"


def write_cases(lean_file: Path, rocq_file: Path, mutant_file: Path) -> None:
    rows = draw()
    lean = [
        "import GororobaMath.CayleyDickson.AnnihilatorSymmetry",
        "",
        "open CayleyDickson",
        "",
        "/-- The vector of level k whose coordinates the list gives, first half first. -/",
        "def build : (k : Nat) → List Int → Tower Int k",
        "  | 0, l => show Tower Int 0 from l.headD 0",
        "  | k + 1, l => Tower.mk (build k (l.take (2 ^ k))) (build k (l.drop (2 ^ k)))",
        "",
        "def main : IO Unit := do",
    ]
    for k, x, y in rows:
        lean.append(f"  IO.println (Tower.dot {k} (build {k} {lean_list(x)}) (build {k} {lean_list(y)}))")
        lean.append(f"  IO.println (Tower.re {k} (build {k} {lean_list(x)}))")
    lean_file.write_text("\n".join(lean) + "\n", encoding="utf-8")
    head = [
        "From Stdlib Require Import ZArith List.",
        "Require Import CdImaginarySumConference.",
        "Import ListNotations.",
        "Open Scope Z_scope.",
        "",
        "Fixpoint build (k : nat) (l : list Z) : cd k :=",
        "  match k as d return cd d with",
        "  | O => hd 0 l",
        "  | S j => (build j (firstn (Nat.pow 2 j) l), build j (skipn (Nat.pow 2 j) l))",
        "  end.",
        "",
    ]
    mutant = [
        "Fixpoint dot_mutant (k : nat) : cd k -> cd k -> Z :=",
        "  match k as d return cd d -> cd d -> Z with",
        "  | O => Z.mul",
        "  | S j => fun x y => dot_mutant j (fst x) (fst y)",
        "  end.",
        "",
        "Fixpoint re_mutant (k : nat) : cd k -> Z :=",
        "  match k as d return cd d -> Z with",
        "  | O => fun v => v",
        "  | S j => fun v => re_mutant j (snd v)",
        "  end.",
        "",
    ]
    for path, dot, real, extra in ((rocq_file, "dot", "re", []), (mutant_file, "dot_mutant", "re_mutant", mutant)):
        lines = head + extra
        for k, x, y in rows:
            lines.append(f"Eval vm_compute in {dot} {k} (build {k} {rocq_list(x)}) (build {k} {rocq_list(y)}).")
            lines.append(f"Eval vm_compute in {real} {k} (build {k} {rocq_list(x)}).")
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def read_lean(path: Path) -> list[int]:
    return [int(line) for line in path.read_text(encoding="utf-8").split()]


def read_rocq(path: Path) -> list[int]:
    return [int(m.group(1)) for line in path.read_text(encoding="utf-8").splitlines() if (m := EVAL.match(line))]


def main() -> int:
    if len(sys.argv) == 5 and sys.argv[1] == "cases":
        write_cases(Path(sys.argv[2]), Path(sys.argv[3]), Path(sys.argv[4]))
        return 0
    if len(sys.argv) == 4 and sys.argv[1] == "compare":
        try:
            lean = read_lean(Path(sys.argv[2]))
            rocq = read_rocq(Path(sys.argv[3]))
        except (OSError, ValueError) as error:
            print(f"compare_dot: {error}", file=sys.stderr)
            return 2
        expected = 2 * PER_LEVEL * len(LEVELS)
        if len(lean) != expected or len(rocq) != expected:
            print(
                f"compare_dot: expected {expected} values, Lean printed {len(lean)}, Rocq {len(rocq)}", file=sys.stderr
            )
            return 2
        for index, (a, b) in enumerate(zip(lean, rocq, strict=True)):
            if a != b:
                print(f"compare_dot: value {index} differs: Lean {a}, Rocq {b}", file=sys.stderr)
                return 1
        print(f"compare_dot: {expected} values agree")
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
