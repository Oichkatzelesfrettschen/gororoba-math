"""Cases and comparison for ci/compare_bordered_matrix.sh: the bordered matrix of PfaffianSixteen in Lean and Rocq.

Usage:

    "$PYTHON" -I -B ci/compare_bordered_matrix.py cases LEAN_FILE QUANTUM_DIR
    "$PYTHON" -I ci/compare_bordered_matrix.py closure TARGET.v < DEP_OUTPUT
    "$PYTHON" -I -B ci/compare_bordered_matrix.py compare LEAN_OUTPUT ROCQ_OUTPUT
    "$PYTHON" -I -B ci/compare_bordered_matrix.py rows LEAN_OUTPUT ROCQ_OUTPUT

`cases` draws SEEDS pairs of integer vectors (z, t), indexed 1 to 15, from a fixed seed: entries of both
signs, and a z with zeros at every fourth seed. It writes a Lean program that prints, per seed, the 256
entries `PfaffianSixteen.borderedA z t a b` for a, b below 16 in row-major order and then
`PfaffianSixteen.rhsv z t`, and after the seeds the value of `Matrix.pfaffian` of
`PfaffianSixteenSchur.A16 z t` at the seeds of PF_SEEDS. Into QUANTUM_DIR (a copy of rocq/quantum) it
writes CompareBordered.v, which evaluates the polynomials `Amat a b` and `rhs` of
StiefelA5Certificate.v at the same vectors through `ev` of StiefelA5Pfaffian.v instantiated at the
integers, and the Pfaffian `P.pf` of PfaffianTheory over the evaluated matrix, and two mutated
references: CompareBorderedSign.v negates `Amat 3 5`, CompareBorderedSwap.v exchanges z and t.

`compare` exits 0 when every entry, every right-hand side and every Pfaffian of the two outputs agree
(the Lean Pfaffian equals the Rocq Pfaffian and the Rocq `rhs` of its seed), 1 on the first difference,
and 2 when an output is unreadable or incomplete. `rows` does the same for the entries and right-hand
sides of a mutant output, which holds no Pfaffians.

`closure` reads the output of rocq dep on standard input and prints, in dependency order, the sources
of the directory that TARGET.v requires, TARGET.v last."""

import os
import random
import re
import sys
from pathlib import Path

SEEDS = 24
PF_SEEDS = (0, 3, 7)
SEED = 20261125
BLOCK = 16 * 16 + 1
SIGN_PAIR = (3, 5)


def draw() -> list[tuple[list[int], list[int]]]:
    """Returns z and t of each seed as lists of 16 integers whose entry 0 is unused and 0."""
    rng = random.Random(SEED)  # noqa: S311 - reproducible test vectors, not secrets
    out = []
    for i in range(SEEDS):
        z = [0] + [rng.choice((-1, 1)) * rng.randint(1, 9) for _ in range(15)]
        t = [0] + [rng.choice((-1, 1)) * rng.randint(1, 9) for _ in range(15)]
        if i % 4 == 3:
            for k in rng.sample(range(1, 16), 6):
                z[k] = 0
        out.append((z, t))
    return out


def lean_list(values: list[int]) -> str:
    return "[" + ", ".join(f"({v} : ℤ)" for v in values) + "]"


def rocq_list(values: list[int]) -> str:
    return "[" + "; ".join(f"({v})" for v in values) + "]"


def lean_program(cases: list[tuple[list[int], list[int]]]) -> str:
    lines = [
        "import GororobaMath.LinearAlgebra.PfaffianSixteenSchur",
        "",
        "open PfaffianSixteen PfaffianSixteenSchur",
        "",
        "def vec (l : List ℤ) (k : ℕ) : ℤ := l.getD k 0",
        "",
        "def printSeed (zs ts : List ℤ) : IO Unit := do",
        "  let z := vec zs",
        "  let t := vec ts",
        "  for a in List.range 16 do",
        "    for b in List.range 16 do",
        "      IO.println (borderedA z t a b)",
        "  IO.println (rhsv z t)",
        "",
        "def printPf (zs ts : List ℤ) : IO Unit :=",
        "  IO.println (Matrix.pfaffian (A16 (vec zs) (vec ts)))",
        "",
        "def main : IO Unit := do",
    ]
    for z, t in cases:
        lines.append(f"  printSeed {lean_list(z)} {lean_list(t)}")
    for i in PF_SEEDS:
        z, t = cases[i]
        lines.append(f"  printPf {lean_list(z)} {lean_list(t)}")
    return "\n".join(lines) + "\n"


def rocq_program(cases: list[tuple[list[int], list[int]]], mutant: str | None) -> str:
    """The Rocq evaluation; `mutant` is None, "sign" or "swap"; only the reference prints Pfaffians."""
    a, b = SIGN_PAIR
    lines = [
        "From Stdlib Require Import List ZArith Ring InitialRing.",
        "Require Import CdTowerRing StiefelA5Certificate StiefelA5Pfaffian.",
        "Import ListNotations.",
        "Local Open Scope Z_scope.",
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
        "Module SZ := StiefelPfaffian ZR.",
        "",
    ]
    if mutant == "sign":
        lines.append(
            f"Definition Aref (a b : nat) : ZP := "
            f"if andb (Nat.eqb a {a}) (Nat.eqb b {b}) then popp (Amat a b) else Amat a b."
        )
    else:
        lines.append("Definition Aref (a b : nat) : ZP := Amat a b.")
    lines += [
        "",
        "Definition entries (env : list Z) (a : nat) : list Z :=",
        "  map (fun b => SZ.ev env (Aref a b)) (seq 0 16).",
        "Definition rows (env : list Z) : list Z :=",
        "  flat_map (entries env) (seq 0 16) ++ [SZ.ev env rhs].",
        "Definition pfaffian (env : list Z) : Z :=",
        "  let tab := map (entries env) (seq 0 16) in",
        "  SZ.P.pf (fun a b => nth b (nth a tab []) 0) idx.",
        "",
    ]
    for z, t in cases:
        zs, ts = rocq_list(z[1:]), rocq_list(t[1:])
        env = f"({ts} ++ {zs})" if mutant == "swap" else f"({zs} ++ {ts})"
        lines.append(f"Eval vm_compute in (rows {env}).")
    if mutant is None:
        for i in PF_SEEDS:
            z, t = cases[i]
            lines.append(f"Eval vm_compute in (pfaffian ({rocq_list(z[1:])} ++ {rocq_list(t[1:])})).")
    return "\n".join(lines) + "\n"


def write_cases(lean_file: Path, quantum_dir: Path) -> None:
    cases = draw()
    lean_file.write_text(lean_program(cases), encoding="utf-8")
    for name, mutant in (("CompareBordered", None), ("CompareBorderedSign", "sign"), ("CompareBorderedSwap", "swap")):
        (quantum_dir / f"{name}.v").write_text(rocq_program(cases, mutant), encoding="utf-8")


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


def rocq_lists(text: str) -> list[list[int]]:
    """Returns the integers of each `Eval` result of a Rocq output, in order."""
    results = []
    for segment in re.split(r"\n\s*:\s*(?:list Z|Z)\s*(?:\n|$)", text):
        if "=" not in segment:
            continue
        results.append([int(m) for m in re.findall(r"-?\d+", segment.split("=", 1)[1])])
    return results


def compare(lean_path: Path, rocq_path: Path, with_pfaffians: bool) -> int:
    try:
        lean = [int(line) for line in lean_path.read_text(encoding="utf-8").split()]
        rocq = rocq_lists(rocq_path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        print(f"compare_bordered_matrix: {error}", file=sys.stderr)
        return 2
    pf_count = len(PF_SEEDS) if with_pfaffians else 0
    if len(lean) != SEEDS * BLOCK + len(PF_SEEDS) or len(rocq) != SEEDS + pf_count:
        print(
            f"compare_bordered_matrix: expected {SEEDS * BLOCK + len(PF_SEEDS)} Lean values and "
            f"{SEEDS + pf_count} Rocq results, got {len(lean)} and {len(rocq)}",
            file=sys.stderr,
        )
        return 2
    if any(len(block) != BLOCK for block in rocq[:SEEDS]) or any(len(r) != 1 for r in rocq[SEEDS:]):
        print("compare_bordered_matrix: a Rocq result has the wrong length", file=sys.stderr)
        return 2
    for s in range(SEEDS):
        for k, (x, y) in enumerate(zip(lean[s * BLOCK : (s + 1) * BLOCK], rocq[s], strict=True)):
            if x != y:
                where = f"entry ({k // 16}, {k % 16})" if k < BLOCK - 1 else "the right-hand side"
                print(f"compare_bordered_matrix: seed {s}, {where}: Lean {x}, Rocq {y}", file=sys.stderr)
                return 1
    if with_pfaffians:
        lean_pf = lean[SEEDS * BLOCK :]
        for j, s in enumerate(PF_SEEDS):
            rhs = rocq[s][BLOCK - 1]
            if not lean_pf[j] == rocq[SEEDS + j][0] == rhs:
                print(
                    f"compare_bordered_matrix: seed {s} Pfaffian: Lean {lean_pf[j]}, Rocq {rocq[SEEDS + j][0]}, "
                    f"Rocq rhs {rhs}",
                    file=sys.stderr,
                )
                return 1
    nonzero = sum(1 for s in range(SEEDS) for x in lean[s * BLOCK : (s + 1) * BLOCK] if x != 0)
    print(
        f"compare_bordered_matrix: {SEEDS} seeds, {SEEDS * 256} matrix entries ({nonzero} nonzero with the "
        f"right-hand sides) and {pf_count} Pfaffians agree in Lean and Rocq"
    )
    return 0


def main() -> int:
    args = sys.argv[1:]
    if len(args) == 3 and args[0] == "cases":
        try:
            write_cases(Path(args[1]), Path(args[2]))
        except OSError as error:
            print(f"compare_bordered_matrix: {error}", file=sys.stderr)
            return 2
        return 0
    if len(args) == 2 and args[0] == "closure":
        try:
            print("\n".join(closure(args[1], sys.stdin.read())))
        except ValueError as error:
            print(f"compare_bordered_matrix: {error}", file=sys.stderr)
            return 2
        return 0
    if len(args) == 3 and args[0] in ("compare", "rows"):
        return compare(Path(args[1]), Path(args[2]), args[0] == "compare")
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
