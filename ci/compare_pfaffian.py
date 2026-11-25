"""Cases and comparison for ci/compare_pfaffian.sh: Lean and Rocq Pfaffians over the integers.

Usage:

    "$PYTHON" -I -B ci/compare_pfaffian.py cases LEAN_FILE QUANTUM_DIR
    "$PYTHON" -I ci/compare_pfaffian.py closure TARGET.v < DEP_OUTPUT
    "$PYTHON" -I -B ci/compare_pfaffian.py compare LEAN_OUTPUT ROCQ_OUTPUT

`cases` writes a Lean program that prints Matrix.pfaffianAux A l of
lean/GororobaMath/LinearAlgebra/Pfaffian.lean for the integer matrices and index lists of CASES, one
integer per line; into QUANTUM_DIR (a copy of rocq/quantum) a Rocq file ComparePfaffian.v that evaluates
pf M l of PfaffianTheory in rocq/quantum/Pfaffian.v, instantiated at the integers, on the same cases with
vm_compute, one Eval per case printing the pair (positive part, negative part) of the value; and a
mutated reference, PfaffianMutant.v (the definitions of Pfaffian.v up to pf, with the alternating sign
of the expansion replaced by one) with ComparePfaffianMutant.v, the same evaluation against it. A matrix
is a function of two natural-number indices, and the index list holds natural numbers, in both provers.

`closure` reads the output of rocq dep on standard input and prints, in dependency order, the sources
of the directory that TARGET.v requires, TARGET.v last.

`compare` reads the integers the Lean program printed and the pairs Rocq printed and exits 0 when both
hold one value per case and agree, 1 on the first difference, and 2 when an output is unreadable or
incomplete."""

import os
import re
import sys
from pathlib import Path

# name: (Lean body of a function ℕ → ℕ → ℤ, Rocq body of a function nat -> nat -> Z)
MATRICES = {
    "skewLinear": (
        "if a < b then ((3 * a + 7 * b + 1 : ℕ) : ℤ) else if b < a then -((3 * b + 7 * a + 1 : ℕ) : ℤ) else 0",
        "if Nat.ltb a b then Z.of_nat (3 * a + 7 * b + 1) "
        "else if Nat.ltb b a then Z.opp (Z.of_nat (3 * b + 7 * a + 1)) else 0%Z",
    ),
    "skewProduct": (
        "if a < b then ((a * b + 1 : ℕ) : ℤ) else if b < a then -((b * a + 1 : ℕ) : ℤ) else 0",
        "if Nat.ltb a b then Z.of_nat (a * b + 1) else if Nat.ltb b a then Z.opp (Z.of_nat (b * a + 1)) else 0%Z",
    ),
    "general": (
        "((a + 1) * (b + 2) + 2 * a * a : ℕ)",
        "Z.of_nat ((a + 1) * (b + 2) + 2 * a * a)",
    ),
}
SKEW_LISTS = [list(range(n)) for n in range(9)] + [
    [2, 0, 3, 1],
    [3, 1, 4, 0, 5, 2],
    [7, 2, 5, 0, 4, 1, 6, 3],
    [7, 6, 5, 4, 3, 2, 1, 0],
    [1, 3, 4, 7, 9, 2],
    [10, 3, 8, 5],
    [0, 1, 1, 2],
    [0, 1, 2, 0],
    [2, 2],
    [0, 1, 2, 3, 3, 5],
    [3, 0, 1, 2, 3, 4, 5, 6],
    [1, 4, 6, 2, 9],
    [5],
]
GENERAL_LISTS = [list(range(n)) for n in range(7)] + [
    [2, 0, 3, 1],
    [3, 1, 4, 0, 5, 2],
    [0, 1, 1, 2],
    [4, 1, 7, 2],
]
CASES = [(name, lst) for name in ("skewLinear", "skewProduct") for lst in SKEW_LISTS] + [
    ("general", lst) for lst in GENERAL_LISTS
]
PAIR = re.compile(r"=\s*\(\s*(\d+)(?:%N)?\s*,\s*(\d+)(?:%N)?\s*\)")
SIGN_TERM = "(fun k => (sgn k * M x (nth k r O) * pfn n' (rem_at k r))%pf)"
MUTANT_TERM = "(fun k => (D.one * M x (nth k r O) * pfn n' (rem_at k r))%pf)"
DEFINITION_END = "Definition pf (l : list nat) : D.t := pfn (length l) l."


def lean_list(lst: list[int]) -> str:
    return "[" + ", ".join(str(i) for i in lst) + "]"


def rocq_list(lst: list[int]) -> str:
    return "[" + "; ".join(str(i) for i in lst) + "]"


def mutant_source(source: str) -> str:
    if source.count(SIGN_TERM) != 1 or source.count(DEFINITION_END) != 1:
        raise ValueError("Pfaffian.v does not hold the expansion term or the definition of pf the mutant edits")
    head = source.split(DEFINITION_END, 1)[0] + DEFINITION_END
    return head.replace(SIGN_TERM, MUTANT_TERM) + "\n\nEnd WithM.\n\nEnd PfaffianTheory.\n"


def rocq_file(module: str, evals: bool) -> str:
    lines = [
        "From Stdlib Require Import List ZArith Ring InitialRing.",
        f"Require Import CdTowerRing {module}.",
        "Import ListNotations.",
        "",
        "Module ZR <: CommutativeRing.",
        "  Definition t := Z.",
        "  Definition zero := 0%Z.",
        "  Definition one := 1%Z.",
        "  Definition add := Z.add.",
        "  Definition mul := Z.mul.",
        "  Definition sub := Z.sub.",
        "  Definition opp := Z.opp.",
        "  Lemma ring_th : ring_theory zero one add mul sub opp (@eq t). Proof. exact Zth. Qed.",
        "End ZR.",
        "",
        "Module PZ := PfaffianTheory ZR.",
        "",
    ]
    for name, (_, rocq) in MATRICES.items():
        lines.append(f"Definition {name} (a b : nat) : Z := {rocq}.")
    lines.append("")
    if evals:
        for name, lst in CASES:
            lines.append(
                f"Eval vm_compute in (let x := PZ.pf {name} {rocq_list(lst)} in "
                "(Z.to_N (Z.max 0 x), Z.to_N (Z.max 0 (Z.opp x))))."
            )
    return "\n".join(lines) + "\n"


def write_cases(lean_file: Path, quantum_dir: Path) -> None:
    lean = [
        "import GororobaMath.LinearAlgebra.Pfaffian",
        "",
        "open Matrix",
        "",
    ]
    for name, (body, _) in MATRICES.items():
        lean.append(f"def {name} (a b : ℕ) : ℤ := {body}")
    lean += ["", "def main : IO Unit := do"]
    for name, lst in CASES:
        lean.append(f"  IO.println (pfaffianAux {name} {lean_list(lst)})")
    lean_file.write_text("\n".join(lean) + "\n", encoding="utf-8")
    source = (quantum_dir / "Pfaffian.v").read_text(encoding="utf-8")
    (quantum_dir / "PfaffianMutant.v").write_text(mutant_source(source), encoding="utf-8")
    (quantum_dir / "ComparePfaffian.v").write_text(rocq_file("Pfaffian", True), encoding="utf-8")
    (quantum_dir / "ComparePfaffianMutant.v").write_text(rocq_file("PfaffianMutant", True), encoding="utf-8")


def closure(target: str, dep_output: str) -> list[str]:
    deps: dict[str, list[str]] = {}
    for line in dep_output.replace("\\\n", " ").splitlines():
        if ":" not in line:
            continue
        lhs, rhs = line.split(":", 1)
        objects = [t for t in lhs.split() if t.endswith(".vo")]
        if not objects:
            continue
        source = os.path.normpath(objects[0][:-3] + ".v")
        required = [os.path.normpath(t[:-3] + ".v") for t in rhs.split() if t.endswith(".vo")]
        deps[source] = [r for r in required if r != source]
    target = os.path.normpath(target)
    if target not in deps:
        raise ValueError(f"rocq dep lists no {target}")
    order: list[str] = []
    seen: set[str] = set()

    def visit(source: str) -> None:
        if source in seen:
            return
        seen.add(source)
        for dep in deps.get(source, []):
            visit(dep)
        order.append(source)

    visit(target)
    missing = [s for s in order if s not in deps]
    if missing:
        raise ValueError(f"the closure of {target} needs sources outside the directory: {missing}")
    return order


def compare(lean_path: Path, rocq_path: Path) -> int:
    try:
        lean = [int(line) for line in lean_path.read_text(encoding="utf-8").split()]
        rocq = [int(m.group(1)) - int(m.group(2)) for m in PAIR.finditer(rocq_path.read_text(encoding="utf-8"))]
    except (OSError, ValueError) as error:
        print(f"compare_pfaffian: {error}", file=sys.stderr)
        return 2
    if len(lean) != len(CASES) or len(rocq) != len(CASES):
        print(
            f"compare_pfaffian: expected {len(CASES)} values, Lean printed {len(lean)}, Rocq {len(rocq)}",
            file=sys.stderr,
        )
        return 2
    for (name, lst), a, b in zip(CASES, lean, rocq, strict=True):
        if a != b:
            print(f"compare_pfaffian: {name} on {lst}: Lean {a}, Rocq {b}", file=sys.stderr)
            return 1
    nonzero = sum(1 for a in lean if a != 0)
    print(f"compare_pfaffian: {len(CASES)} Pfaffians ({nonzero} nonzero) agree in Lean and Rocq")
    return 0


def main() -> int:
    args = sys.argv[1:]
    if len(args) == 3 and args[0] == "cases":
        try:
            write_cases(Path(args[1]), Path(args[2]))
        except (OSError, ValueError) as error:
            print(f"compare_pfaffian: {error}", file=sys.stderr)
            return 2
        return 0
    if len(args) == 2 and args[0] == "closure":
        try:
            print("\n".join(closure(args[1], sys.stdin.read())))
        except ValueError as error:
            print(f"compare_pfaffian: {error}", file=sys.stderr)
            return 2
        return 0
    if len(args) == 3 and args[0] == "compare":
        return compare(Path(args[1]), Path(args[2]))
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
