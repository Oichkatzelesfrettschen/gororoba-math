"""Cases and comparison for ci/compare_order_three.sh: Tower.orderThree against OrderThreeMap.psi2.

Usage:

    "$PYTHON" -I ci/compare_order_three.py closure ROCQ_QUANTUM_DIR
    "$PYTHON" -I ci/compare_order_three.py cases LEAN_FILE ROCQ_FILE ROCQ_MUTANT_FILE
    "$PYTHON" -I ci/compare_order_three.py compare LEAN_OUTPUT ROCQ_OUTPUT

`closure` prints, one per line and dependencies first, the sources of rocq/quantum that
CdTowerOrderThreeMap.v requires, itself last. `cases` writes a Lean program that prints the 16 basis
images of Tower.orderThree at level 4 over Z[sqrt 3] (GororobaMath.CayleyDickson.OrderThree), a Rocq
file that prints the same images of Root3Map.psi2 with vm_compute, and a mutated Rocq reference whose
coefficient 3 of the real part is 2. An element lists its 32 integers as 16 pairs (a, b) = a + b sqrt 3,
the first half of each doubled pair first, the order of both trees. `compare` reads the integers each side printed
(Lean one per line, Rocq every integer of the printed value) and exits 0 when both lists are equal and
nonempty, 1 on the first difference, and 2 when an output is unreadable.
"""

import re
import sys
from pathlib import Path

LEVEL = 4
INTS = re.compile(r"-?[0-9]+")
REQUIRE = re.compile(r"^Require\s+(?:Import|Export)?\s*([A-Za-z0-9_\s]+)\.", re.MULTILINE)
TOP = "CdTowerOrderThreeMap"


def closure(directory: Path) -> list[str]:
    order: list[str] = []
    seen: set[str] = set()

    def visit(name: str) -> None:
        if name in seen:
            return
        seen.add(name)
        text = (directory / f"{name}.v").read_text(encoding="utf-8")
        for match in REQUIRE.finditer(text):
            for word in match.group(1).split():
                if (directory / f"{word}.v").is_file():
                    visit(word)
        order.append(name)

    visit(TOP)
    return order


def write_cases(lean_file: Path, rocq_file: Path, mutant_file: Path) -> None:
    size = 2**LEVEL
    lean = [
        "import Mathlib.NumberTheory.Zsqrtd.Basic",
        "import GororobaMath.CayleyDickson.OrderThree",
        "",
        "open CayleyDickson",
        "",
        "def Z3 := Zsqrtd 3",
        "instance : CommRing Z3 := inferInstanceAs (CommRing (Zsqrtd 3))",
        "instance : StarRing Z3 := starRingOfComm",
        "instance : TrivialStar Z3 := ⟨fun _ => rfl⟩",
        "",
        "def r3 : Z3 := (⟨0, 1⟩ : Zsqrtd 3)",
        "",
        "def flat : (k : Nat) → Tower Z3 k → List Int",
        "  | 0, x => [(show Zsqrtd 3 from x).re, (show Zsqrtd 3 from x).im]",
        "  | k + 1, x => flat k (CayleyDickson.re x) ++ flat k (CayleyDickson.im x)",
        "",
        "def main : IO Unit := do",
    ]
    for i in range(size):
        lean.append(
            f"  for v in flat {LEVEL} (Tower.orderThree r3 (Tower.e Z3 {LEVEL} (BitVec.ofNat {LEVEL} {i}))) do "
            "IO.println v"
        )
    lean_file.write_text("\n".join(lean) + "\n", encoding="utf-8")
    head = [
        "From Stdlib Require Import ZArith List.",
        "Require Import CdTowerOrderThreeMap.",
        "Import ListNotations.",
        "Open Scope Z_scope.",
        "",
    ]
    mutant = [
        "Module M := Root3Map.",
        "Import M.BC.",
        "Definition two' : Root3Integers.t := Root3Integers.add Root3Integers.one Root3Integers.one.",
        "Definition imaginary' k (y : TB.cd k) : TB.cd k :=",
        "  TB.add k y (TB.scale k (Root3Integers.opp (TB.re k y)) (TB.one k)).",
        "Definition psi2_mutant k (x : TB.cd (S k)) : TB.cd (S k) :=",
        "  (TB.add k (TB.add k (TB.scale k (Root3Integers.mul two' (TB.re k (fst x))) (TB.one k))",
        "                      (TB.scale k TB.neg_one (fst x)))",
        "            (TB.scale k Root3Integers.r3 (imaginary' k (snd x))),",
        "   TB.add k (TB.add k (TB.scale k (Root3Integers.mul two' (TB.re k (snd x))) (TB.one k))",
        "                      (TB.scale k TB.neg_one (snd x)))",
        "            (TB.scale k (Root3Integers.opp Root3Integers.r3) (imaginary' k (fst x)))).",
        "",
    ]
    for path, fn, extra in ((rocq_file, "Root3Map.psi2", []), (mutant_file, "psi2_mutant", mutant)):
        lines = head + extra
        for i in range(size):
            lines.append(f"Eval vm_compute in {fn} {LEVEL - 1} (Root3Map.BC.SB.basis {LEVEL} {i}).")
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def read_lean(path: Path) -> list[int]:
    return [int(token) for token in path.read_text(encoding="utf-8").split()]


def read_rocq(path: Path) -> list[int]:
    text = path.read_text(encoding="utf-8")
    values = []
    for block in re.findall(r"=\s(.*?)\n\s+:\s", text, re.DOTALL):
        values.extend(int(token) for token in INTS.findall(block))
    return values


def main() -> int:
    if len(sys.argv) == 3 and sys.argv[1] == "closure":
        print("\n".join(closure(Path(sys.argv[2]))))
        return 0
    if len(sys.argv) == 5 and sys.argv[1] == "cases":
        write_cases(Path(sys.argv[2]), Path(sys.argv[3]), Path(sys.argv[4]))
        return 0
    if len(sys.argv) == 4 and sys.argv[1] == "compare":
        try:
            lean = read_lean(Path(sys.argv[2]))
            rocq = read_rocq(Path(sys.argv[3]))
        except (OSError, ValueError) as error:
            print(f"compare_order_three: {error}", file=sys.stderr)
            return 2
        expected = 2**LEVEL * 2 ** (LEVEL + 1)
        if len(lean) != expected or len(rocq) != expected:
            print(
                f"compare_order_three: expected {expected} values, Lean printed {len(lean)}, Rocq {len(rocq)}",
                file=sys.stderr,
            )
            return 2
        for index, (a, b) in enumerate(zip(lean, rocq, strict=True)):
            if a != b:
                print(f"compare_order_three: value {index} differs: Lean {a}, Rocq {b}", file=sys.stderr)
                return 1
        print(f"compare_order_three: {expected} values agree")
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
