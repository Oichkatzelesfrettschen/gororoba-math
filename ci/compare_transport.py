"""Cases and comparison for ci/compare_transport.sh: the transport coordinates of PureDoublingTransport.

Usage:

    "$PYTHON" -I -B ci/compare_transport.py cases LEAN_FILE QUANTUM_DIR
    "$PYTHON" -I ci/compare_transport.py closure TARGET.v < DEP_OUTPUT
    "$PYTHON" -I -B ci/compare_transport.py compare LEAN_OUTPUT ROCQ_OUTPUT

The ring is ZMod P with P = 998244353 (P = 1 mod 4) and I = 911660635, I * I = -1, the identity as star.
`cases` draws SEEDS triples of coordinate vectors (u, y, x) of level 5 (32 coordinates, entries -9 to 9,
the first half of each pair first, the order of both trees) from a fixed seed. It writes a Lean program that
prints, per seed, the 16 coordinates of `Tower.phi I u` and of `Tower.phi (-I) u` and then those of
`Tower.phi I (y * x)` and `Tower.phi (-I) (y * x)`, as natural numbers below P. Into QUANTUM_DIR (a copy
of rocq/quantum) it writes CompareTransport.v, which evaluates `phi` and `psi` of
`StiefelTransport` (StiefelA5Transport.v) at the same elements, built by its `mk`, and at
`T.mul 5 y x`, instantiated at Zmod P, and two mutated references: CompareTransportSign.v negates
coordinate 3 of `phi`, and CompareTransportSwap.v exchanges the two halves of u, y and x.

`compare` exits 0 when the two outputs hold the same values in the same order, 1 on the first
difference, and 2 when an output is unreadable or incomplete.

`closure` reads the output of rocq dep on standard input and prints, in dependency order, the sources
of the directory that TARGET.v requires, TARGET.v last."""

import os
import random
import re
import sys
from pathlib import Path

SEEDS = 24
SEED = 20261126
P = 998244353
I = 911660635  # noqa: E741 - the square root of -1 modulo P, named as in the sources
BLOCK = 64
SIGN_COORD = 3
SIZE = 32


def draw() -> list[tuple[list[int], list[int], list[int]]]:
    """Returns u, y and x of each seed as lists of 32 integers."""
    require(I * I % P == P - 1, "I is not a square root of -1 modulo P")
    rng = random.Random(SEED)  # noqa: S311 - reproducible test vectors, not secrets
    out = []
    for _ in range(SEEDS):
        u, y, x = ([rng.randint(-9, 9) for _ in range(SIZE)] for _ in range(3))
        out.append((u, y, x))
    return out


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def lean_list(values: list[int]) -> str:
    return "[" + ", ".join(f"({v} : ℤ)" for v in values) + "]"


def rocq_list(values: list[int]) -> str:
    return "[" + "; ".join(f"({v})" for v in values) + "]"


def lean_program(cases: list[tuple[list[int], list[int], list[int]]]) -> str:
    lines = [
        "import GororobaMath.CayleyDickson.PureDoublingTransport",
        "",
        "open CayleyDickson",
        "",
        f"local instance : StarRing (ZMod {P}) := starRingOfComm",
        "",
        "def vec (l : List ℤ) (k : ℕ) : ZMod " + str(P) + " := ((l.getD k 0 : ℤ) : ZMod " + str(P) + ")",
        "",
        f"def build : (k : ℕ) → (ℕ → ZMod {P}) → Tower (ZMod {P}) k",
        "  | 0, f => f 0",
        "  | k + 1, f => Tower.mk (build k f) (build k fun i => f (i + 2 ^ k))",
        "",
        f"def coords : (k : ℕ) → Tower (ZMod {P}) k → List (ZMod {P})",
        "  | 0, x => [x]",
        "  | k + 1, ⟨a, b⟩ => coords k a ++ coords k b",
        "",
        f"def out (xs : List (ZMod {P})) : IO Unit := do",
        "  for x in xs do",
        "    IO.println x.val",
        "",
        "def printSeed (us ys xs : List ℤ) : IO Unit := do",
        f"  let ι : ZMod {P} := {I}",
        "  let u := build 5 (vec us)",
        "  let p := build 5 (vec ys) * build 5 (vec xs)",
        "  out (coords 4 (Tower.phi (k := 4) ι u))",
        "  out (coords 4 (Tower.phi (k := 4) (-ι) u))",
        "  out (coords 4 (Tower.phi (k := 4) ι p))",
        "  out (coords 4 (Tower.phi (k := 4) (-ι) p))",
        "",
        "def main : IO Unit := do",
    ]
    lines += [f"  printSeed {lean_list(u)} {lean_list(y)} {lean_list(x)}" for u, y, x in cases]
    return "\n".join(lines) + "\n"


def rocq_program(cases: list[tuple[list[int], list[int], list[int]]], mutant: str | None) -> str:
    """The Rocq evaluation; `mutant` is None, "sign" or "swap"."""
    lines = [
        "From Stdlib Require Import List ZArith Zmod Ring.",
        "Require Import CdTowerRing StiefelA5Transport.",
        "Import ListNotations.",
        "Local Open Scope Z_scope.",
        "",
        "Module ZP <: CommutativeRingWithI.",
        f"  Definition t := Zmod {P}.",
        "  Definition zero : t := Zmod.zero.",
        "  Definition one : t := Zmod.one.",
        "  Definition add : t -> t -> t := Zmod.add.",
        "  Definition mul : t -> t -> t := Zmod.mul.",
        "  Definition sub : t -> t -> t := Zmod.sub.",
        "  Definition opp : t -> t := Zmod.opp.",
        "  Lemma ring_th : ring_theory zero one add mul sub opp (@eq t).",
        f"  Proof. exact (Zmod.ring_theory {P}). Qed.",
        f"  Definition i : t := Zmod.of_Z {P} {I}.",
        "  Lemma i_squared : mul i i = opp one.",
        "  Proof. vm_compute. reflexivity. Qed.",
        "End ZP.",
        "",
        "Module ST := StiefelTransport ZP.",
        "",
        f"Definition vec (l : list Z) (k : nat) : ZP.t := Zmod.of_Z {P} (nth k l 0).",
        "Definition sw (v : ST.T.cd 5) : ST.T.cd 5 := (snd v, fst v).",
    ]
    if mutant == "sign":
        lines.append(
            f"Definition phi_ref (v : ST.T.cd 5) (c : nat) : ZP.t := "
            f"if Nat.eqb c {SIGN_COORD} then ZP.opp (ST.phi v c) else ST.phi v c."
        )
    else:
        lines.append("Definition phi_ref (v : ST.T.cd 5) (c : nat) : ZP.t := ST.phi v c.")
    body = "sw v0" if mutant == "swap" else "v0"
    lines += [
        "",
        "Definition outs (v0 : ST.T.cd 5) : list Z :=",
        f"  let v := {body} in",
        "  map (fun c => Zmod.to_Z (phi_ref v c)) (seq 0 16) ++ map (fun c => Zmod.to_Z (ST.psi v c)) (seq 0 16).",
        "Definition block (u y x : list Z) : list Z :=",
        "  outs (ST.mk 5 (vec u)) ++ outs (ST.T.mul 5 (ST.mk 5 (vec y)) (ST.mk 5 (vec x))).",
        "",
    ]
    lines += [f"Eval vm_compute in (block {rocq_list(u)} {rocq_list(y)} {rocq_list(x)})." for u, y, x in cases]
    return "\n".join(lines) + "\n"


def write_cases(lean_file: Path, quantum_dir: Path) -> None:
    cases = draw()
    lean_file.write_text(lean_program(cases), encoding="utf-8")
    for name, mutant in (
        ("CompareTransport", None),
        ("CompareTransportSign", "sign"),
        ("CompareTransportSwap", "swap"),
    ):
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


def compare(lean_path: Path, rocq_path: Path) -> int:
    try:
        lean = [int(line) for line in lean_path.read_text(encoding="utf-8").split()]
        rocq = rocq_lists(rocq_path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        print(f"compare_transport: {error}", file=sys.stderr)
        return 2
    if len(lean) != SEEDS * BLOCK or len(rocq) != SEEDS or any(len(block) != BLOCK for block in rocq):
        print(
            f"compare_transport: expected {SEEDS * BLOCK} Lean values and {SEEDS} Rocq blocks of {BLOCK}, "
            f"got {len(lean)} and {len(rocq)}",
            file=sys.stderr,
        )
        return 2
    names = ("phi u", "psi u", "phi (y x)", "psi (y x)")
    for s in range(SEEDS):
        for k, (x, y) in enumerate(zip(lean[s * BLOCK : (s + 1) * BLOCK], rocq[s], strict=True)):
            if x != y:
                print(
                    f"compare_transport: seed {s}, {names[k // 16]}, coordinate {k % 16}: Lean {x}, Rocq {y}",
                    file=sys.stderr,
                )
                return 1
    nonzero = sum(1 for x in lean if x != 0)
    print(
        f"compare_transport: {SEEDS} seeds, {SEEDS * BLOCK} coordinates of phi and psi of u and of y * x "
        f"({nonzero} nonzero) agree in Lean and Rocq over ZMod {P}"
    )
    return 0


def main() -> int:
    args = sys.argv[1:]
    if len(args) == 3 and args[0] == "cases":
        try:
            write_cases(Path(args[1]), Path(args[2]))
        except (OSError, ValueError) as error:
            print(f"compare_transport: {error}", file=sys.stderr)
            return 2
        return 0
    if len(args) == 2 and args[0] == "closure":
        try:
            print("\n".join(closure(args[1], sys.stdin.read())))
        except ValueError as error:
            print(f"compare_transport: {error}", file=sys.stderr)
            return 2
        return 0
    if len(args) == 3 and args[0] == "compare":
        return compare(Path(args[1]), Path(args[2]))
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
