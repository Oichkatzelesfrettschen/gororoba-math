"""Cases and comparison for ci/compare_complexification.sh: the base change along the real embedding.

Usage:

    "$PYTHON" -I -B ci/compare_complexification.py cases LEAN_FILE QUANTUM_DIR
    "$PYTHON" -I ci/compare_complexification.py closure TARGET.v < DEP_OUTPUT
    "$PYTHON" -I -B ci/compare_complexification.py compare LEAN_OUTPUT ROCQ_OUTPUT

The real ring is the integers and the complex ring the Gaussian integers, whose real and imaginary parts
are the coordinates of a complex tower element. Lean (lean/GororobaMath/CayleyDickson/BaseChange.lean and
StiefelRealZeroDivisor.lean) reads the Gaussian integers as a wrapper GI with the identity as star, like
TrivStarComplex, and takes Tower.map along Int.castRingHom GI; the real and imaginary parts are Zsqrtd.re
and Zsqrtd.im of the coordinates. Rocq (rocq/quantum/StiefelA5Real.v) evaluates emb, re, im and the
products CT.mul and RT.mul over its real numbers, which no evaluator reduces to numbers, so the Rocq
output keeps each coordinate as a term of +, -, * on 0, 1 and a placeholder lit n for the real number
chosen for the integer n (a parameter of the evaluation file). Each term is read back as an integer
with lit n = n, a ring homomorphism from the integers into the reals, so the Rocq coordinate is
compared with the Lean coordinate as an integer.

Per case (level k, n = 2^k coordinates; y real, x complex with the parts xr and xi), both sides print
eight blocks of n integers: the real and imaginary coordinates of the image of y (Lean map, Rocq emb);
the real and imaginary parts of x; the real and imaginary parts of the product of the image of y with x;
and y * xr and y * xi (the Lean step map y * x = map (y * xr) + I * map (y * xi), whose real and
imaginary parts are these two blocks, and the Rocq right-hand sides of mul_emb). Levels 4 and 5 carry
16 and 8 seeded cases, entries -9 to 9.

cases writes the Lean program and, into QUANTUM_DIR (a copy of rocq/quantum), CompareComplexification.v
and two mutated references: CompareComplexificationSwap.v exchanges re and im, and
CompareComplexificationSign.v negates coordinate 3 of the real element that emb embeds.

compare exits 0 when the two outputs hold the same values in the same order, 1 on the first difference,
and 2 when an output is unreadable or incomplete.

closure reads the output of rocq dep on standard input and prints, in dependency order, the sources of
the directory that TARGET.v requires, TARGET.v last."""

import os
import random
import re
import sys
from pathlib import Path

sys.setrecursionlimit(20000)

SEED = 20261127
LEVELS = ((4, 16), (5, 8))
SIGN_COORD = 3
BLOCKS = (
    "emb y real",
    "emb y imaginary",
    "x real",
    "x imaginary",
    "emb y * x real",
    "emb y * x imaginary",
    "y * re x",
    "y * im x",
)

Case = tuple[int, list[int], list[int], list[int]]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def draw() -> list[Case]:
    """Returns (level, y, xr, xi) per case, each vector of 2^level integers."""
    rng = random.Random(SEED)  # noqa: S311 - reproducible test vectors, not secrets
    out = []
    for level, seeds in LEVELS:
        size = 2**level
        for _ in range(seeds):
            y, xr, xi = ([rng.randint(-9, 9) for _ in range(size)] for _ in range(3))
            out.append((level, y, xr, xi))
    return out


def lean_list(values: list[int]) -> str:
    return "[" + ", ".join(f"({v} : ℤ)" for v in values) + "]"


def rocq_list(values: list[int]) -> str:
    return "[" + "; ".join(f"({v})" for v in values) + "]%Z"


LEAN_HEAD = """import GororobaMath.CayleyDickson.StiefelRealZeroDivisor
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

open CayleyDickson

def GI : Type := GaussianInt

namespace GI

instance : CommRing GI := inferInstanceAs (CommRing GaussianInt)

instance : Star GI := ⟨id⟩

instance : TrivialStar GI := ⟨fun _ => rfl⟩

instance : StarRing GI where
  star_involutive _ := rfl
  star_mul a b := mul_comm a b
  star_add _ _ := rfl

def mk (a b : ℤ) : GI := (⟨a, b⟩ : GaussianInt)

def re (z : GI) : ℤ := Zsqrtd.re (d := -1) z

def im (z : GI) : ℤ := Zsqrtd.im (d := -1) z

def I : GI := mk 0 1

def ofInt : ℤ →+* GI := Int.castRingHom GI

end GI

def buildZ : (k : ℕ) → (ℕ → ℤ) → Tower ℤ k
  | 0, f => f 0
  | k + 1, f => Tower.mk (buildZ k f) (buildZ k fun i => f (i + 2 ^ k))

def buildG : (k : ℕ) → (ℕ → GI) → Tower GI k
  | 0, f => f 0
  | k + 1, f => Tower.mk (buildG k f) (buildG k fun i => f (i + 2 ^ k))

def coordsG : (k : ℕ) → Tower GI k → List GI
  | 0, x => [x]
  | k + 1, ⟨a, b⟩ => coordsG k a ++ coordsG k b

def out (xs : List ℤ) : IO Unit := do
  for x in xs do
    IO.println x

def printCase (k : ℕ) (ys xrs xis : List ℤ) : IO Unit := do
  let y : Tower ℤ k := buildZ k fun i => ys.getD i 0
  let x : Tower GI k := buildG k fun i => GI.mk (xrs.getD i 0) (xis.getD i 0)
  let ym : Tower GI k := Tower.map GI.ofInt k y
  let cx := coordsG k x
  let xr : Tower ℤ k := buildZ k fun i => (cx.getD i 0).re
  let xi : Tower ℤ k := buildZ k fun i => (cx.getD i 0).im
  let p : Tower GI k := ym * x
  let q : Tower GI k := Tower.map GI.ofInt k (y * xr) + GI.I • Tower.map GI.ofInt k (y * xi)
  let cy := coordsG k ym
  let cp := coordsG k p
  let cq := coordsG k q
  out (cy.map GI.re)
  out (cy.map GI.im)
  out (cx.map GI.re)
  out (cx.map GI.im)
  out (cp.map GI.re)
  out (cp.map GI.im)
  out (cq.map GI.re)
  out (cq.map GI.im)

def main : IO Unit := do
"""


def lean_program(cases: list[Case]) -> str:
    lines = [f"  printCase {k} {lean_list(y)} {lean_list(xr)} {lean_list(xi)}" for k, y, xr, xi in cases]
    return LEAN_HEAD + "\n".join(lines) + "\n"


ROCQ_HEAD = """From Stdlib Require Import Reals ZArith List.
Require Import StiefelA5Real.
Import ListNotations.
Local Open Scope Z_scope.

Parameter lit : Z -> R.

Definition vec (l : list Z) (k : nat) : R := lit (nth k l 0).

Fixpoint mkR (k : nat) (f : nat -> R) : RT.cd k :=
  match k as d return RT.cd d with
  | O => f O
  | S j => (mkR j f, mkR j (fun i => f (i + Nat.pow 2 j)%nat))
  end.

Fixpoint mkC (k : nat) (f g : nat -> R) : CT.cd k :=
  match k as d return CT.cd d with
  | O => (f O, g O)
  | S j => (mkC j f g, mkC j (fun i => f (i + Nat.pow 2 j)%nat) (fun i => g (i + Nat.pow 2 j)%nat))
  end.

Fixpoint flatR (k : nat) : RT.cd k -> list R :=
  match k as d return RT.cd d -> list R with
  | O => fun v => [v]
  | S j => fun v => flatR j (fst v) ++ flatR j (snd v)
  end.

Fixpoint flatC (g : R * R -> R) (k : nat) : CT.cd k -> list R :=
  match k as d return CT.cd d -> list R with
  | O => fun v => [g v]
  | S j => fun v => flatC g j (fst v) ++ flatC g j (snd v)
  end.

Definition negCoord (k : nat) (y : RT.cd k) : RT.cd k :=
  mkR k (fun i => if Nat.eqb i %SIGN% then Ropp (nth i (flatR k y) R0) else nth i (flatR k y) R0).

%DEFS%

Definition block (k : nat) (ly lr li : list Z) : list R :=
  let y := mkR k (vec ly) in
  let x := mkC k (vec lr) (vec li) in
  let ey := embX k y in
  let m := CT.mul k ey x in
  flatC fst k ey ++ flatC snd k ey ++ flatR k (reX k x) ++ flatR k (imX k x)
  ++ flatR k (reX k m) ++ flatR k (imX k m)
  ++ flatR k (RT.mul k y (reX k x)) ++ flatR k (RT.mul k y (imX k x)).

Local Open Scope R_scope.
Set Printing Width 100000000.
"""

ROCQ_DEFS = {
    None: "Definition reX := re.\nDefinition imX := im.\nDefinition embX := emb.",
    "swap": "Definition reX := im.\nDefinition imX := re.\nDefinition embX := emb.",
    "sign": (
        "Definition reX := re.\nDefinition imX := im.\nDefinition embX (k : nat) (y : RT.cd k) := emb k (negCoord k y)."
    ),
}


def rocq_program(cases: list[Case], mutant: str | None) -> str:
    """The Rocq evaluation; mutant is None, "swap" or "sign"."""
    head = ROCQ_HEAD.replace("%SIGN%", str(SIGN_COORD)).replace("%DEFS%", ROCQ_DEFS[mutant])
    lines = [
        f"Eval vm_compute in (block {k} {rocq_list(y)} {rocq_list(xr)} {rocq_list(xi)})." for k, y, xr, xi in cases
    ]
    return head + "\n".join(lines) + "\n"


def write_cases(lean_file: Path, quantum_dir: Path) -> None:
    cases = draw()
    lean_file.write_text(lean_program(cases), encoding="utf-8")
    for name, mutant in (
        ("CompareComplexification", None),
        ("CompareComplexificationSwap", "swap"),
        ("CompareComplexificationSign", "sign"),
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
    require(target in deps, f"rocq dep lists no {target}")
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
    require(not missing, f"the closure of {target} needs sources outside the directory: {missing}")
    return order


TOKEN = re.compile(r"\s*(lit|R0|R1|\d+|[-+*();\[\]])")


class Reader:
    """Reads a Rocq list of ring terms in +, -, * over lit n, R0 and R1 into Python integers."""

    def __init__(self, text: str) -> None:
        self.tokens: list[str] = []
        pos = 0
        text = text.rstrip()
        while pos < len(text):
            match = TOKEN.match(text, pos)
            require(match is not None, f"unreadable term text near {text[pos : pos + 40]!r}")
            assert match is not None  # noqa: S101 - narrows the type after require
            self.tokens.append(match.group(1))
            pos = match.end()
        self.at = 0

    def peek(self) -> str | None:
        return self.tokens[self.at] if self.at < len(self.tokens) else None

    def take(self, expected: str | None = None) -> str:
        token = self.peek()
        require(token is not None and (expected is None or token == expected), f"expected {expected}, got {token}")
        self.at += 1
        assert token is not None  # noqa: S101 - narrows the type after require
        return token

    def expr(self) -> int:
        value = self.term()
        while self.peek() in ("+", "-"):
            if self.take() == "+":
                value += self.term()
            else:
                value -= self.term()
        return value

    def term(self) -> int:
        value = self.unary()
        while self.peek() == "*":
            self.take()
            value *= self.unary()
        return value

    def unary(self) -> int:
        if self.peek() == "-":
            self.take()
            return -self.unary()
        return self.atom()

    def atom(self) -> int:
        word = self.take()
        if word == "(":
            value = self.expr()
            self.take(")")
            return value
        if word == "lit":
            return self.atom()
        if word == "R0":
            return 0
        if word == "R1":
            return 1
        require(word.isdigit(), f"unexpected word {word}")
        return int(word)

    def items(self) -> list[int]:
        self.take("[")
        values: list[int] = []
        if self.peek() == "]":
            self.take()
            return values
        while True:
            values.append(self.expr())
            if self.take() == "]":
                break
        require(self.peek() is None, "text after the closing bracket")
        return values


def rocq_lists(text: str) -> list[list[int]]:
    """Returns the integers of each Eval result of a Rocq output, in order."""
    results = []
    for segment in re.split(r"\n\s*:\s*list R\s*(?:\n|$)", text):
        if "=" not in segment:
            continue
        results.append(Reader(segment.split("=", 1)[1].strip()).items())
    return results


def compare(lean_path: Path, rocq_path: Path) -> int:
    cases = draw()
    sizes = [8 * 2**k for k, _, _, _ in cases]
    try:
        lean = [int(line) for line in lean_path.read_text(encoding="utf-8").split()]
        rocq = rocq_lists(rocq_path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        print(f"compare_complexification: {error}", file=sys.stderr)
        return 2
    if len(lean) != sum(sizes) or [len(block) for block in rocq] != sizes:
        print(
            f"compare_complexification: expected {sum(sizes)} Lean values and {len(sizes)} Rocq cases, "
            f"got {len(lean)} values and {len(rocq)} cases",
            file=sys.stderr,
        )
        return 2
    offset = 0
    for index, ((level, _, _, _), size) in enumerate(zip(cases, sizes, strict=True)):
        width = 2**level
        for position, (a, b) in enumerate(zip(lean[offset : offset + size], rocq[index], strict=True)):
            if a != b:
                print(
                    f"compare_complexification: level {level}, case {index}, {BLOCKS[position // width]}, "
                    f"coordinate {position % width}: Lean {a}, Rocq {b}",
                    file=sys.stderr,
                )
                return 1
        offset += size
    nonzero = sum(1 for x in lean if x != 0)
    print(
        f"compare_complexification: {len(cases)} cases at levels 4 and 5, {len(lean)} values "
        f"({nonzero} nonzero) of emb, re, im and the two sides of mul_emb agree in Lean and Rocq "
        "over the integers and the Gaussian integers"
    )
    return 0


def main() -> int:
    args = sys.argv[1:]
    if len(args) == 3 and args[0] == "cases":
        try:
            write_cases(Path(args[1]), Path(args[2]))
        except (OSError, ValueError) as error:
            print(f"compare_complexification: {error}", file=sys.stderr)
            return 2
        return 0
    if len(args) == 2 and args[0] == "closure":
        try:
            print("\n".join(closure(args[1], sys.stdin.read())))
        except ValueError as error:
            print(f"compare_complexification: {error}", file=sys.stderr)
            return 2
        return 0
    if len(args) == 3 and args[0] == "compare":
        return compare(Path(args[1]), Path(args[2]))
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
