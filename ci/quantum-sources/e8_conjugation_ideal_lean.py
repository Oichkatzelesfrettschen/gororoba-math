"""Render lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean from the germ ideals J of the E8-bar Rees scripts.

The input is the one of e8_conjugation_ideal.py (the 27 generators of J_N- and J_N+ of conjugation_map.sing of the
checkout GOROROBA_QUANTUM names, pinned by sha256 and equal to the lists of the retained v2 Rees scripts), read
through that module. The generator parses them as polynomials over Z in i, s1..s9, requires Phi of the k-th
generator of J_N- to equal plus or minus the k-th generator of J_N+, and requires Phi after the flip of s3, s5, s6
to map every generator of J_N- to the generator of J_N+ with no sign; the signs it finds enter the rendered
source, whose proofs check every identity again with ring.

    GOROROBA_QUANTUM=PATH python3 -B ci/quantum-sources/e8_conjugation_ideal_lean.py --check [--source PATH] | --write

--check renders the source and compares it with the tracked Lean module, or with the file --source names (status 1 on
a difference); --write writes the tracked module and takes no other option. Standard library only.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

import e8_conjugation_ideal as base
from quantum_checkout import MATH

TARGET = MATH / "lean" / "GororobaMath" / "CayleyDickson" / "E8ConjugationIdeal.lean"
WIDTH = 100
INDENT = "    "

Poly = base.Poly


def fail(message: str) -> SystemExit:
    print(f"e8_conjugation_ideal_lean: {message}", file=sys.stderr)
    return SystemExit(1)


def flip(poly: Poly) -> Poly:
    """s3 -> -s3, s5 -> -s5, s6 -> -s6, every other variable fixed."""
    out: Poly = {}
    for e, c in poly.items():
        out[e] = (-c if (e[3] + e[5] + e[6]) % 2 else c) + out.get(e, 0)
    return {m: c for m, c in out.items() if c != 0}


def phi_after_flip(poly: Poly) -> Poly:
    """Phi of the flipped polynomial."""
    return base.phi(flip(poly))


def check_flip_character(minus: list[Poly], plus: list[Poly], flags: list[bool]) -> None:
    """Phi after the flip carries generator k of J_N- to generator k of J_N+ with no sign, and the sign of Phi is the
    parity of deg s3 + deg s5 + deg s6 of the generator, which that degree fixes on every monomial."""
    for k, (g, h, positive) in enumerate(zip(minus, plus, flags, strict=True), start=1):
        if phi_after_flip(g) != h:
            raise fail(f"Phi after the flip of s3, s5, s6 maps generator {k} of J_N- to no generator of J_N+")
        parities = {(e[3] + e[5] + e[6]) % 2 for e in g}
        if len(parities) != 1 or (parities == {0}) != positive:
            raise fail(f"generator {k} of J_N- is no eigenvector of the flip of s3, s5, s6 with the sign of Phi")


def term(monomial: base.Monomial, coefficient: int) -> str:
    factors = [str(abs(coefficient))] if abs(coefficient) != 1 else []
    for name, power in zip(base.VARS, monomial, strict=True):
        if power == 1:
            factors.append(name)
        elif power > 1:
            factors.append(f"{name} ^ {power}")
    return " * ".join(factors) if factors else "1"


def render_poly(poly: Poly, closing: str) -> list[str]:
    """The lines of one polynomial, each at most WIDTH columns; an operator ends its line, CLOSING follows the last term."""
    monomials = sorted(poly, key=lambda m: (-sum(m), [-x for x in m]))
    chunks = []
    for n, m in enumerate(monomials):
        text = ("-" if poly[m] < 0 and n == 0 else "") + term(m, poly[m])
        if n + 1 < len(monomials):
            text += " -" if poly[monomials[n + 1]] < 0 else " +"
        else:
            text += closing
        chunks.append(text)
    lines: list[str] = []
    current = ""
    for chunk in chunks:
        if current and len(INDENT + current + " " + chunk) > WIDTH:
            lines.append(current)
            current = chunk
        else:
            current = f"{current} {chunk}" if current else chunk
    lines.append(current)
    return lines


ARGS = "i s1 s2 s3 s4 s5 s6 s7 s8 s9"


def render_gen(prefix: str, side: str, k: int, poly: Poly) -> str:
    lines = render_poly(poly, "")
    used = {n for m in poly for n, power in zip(base.VARS, m, strict=True) if power}
    args = " ".join(n if n in used else "_" + n for n in base.VARS)
    body = "\n".join(("  " if j == 0 else "    ") + line for j, line in enumerate(lines))
    return f"/-- Generator §{k}§ of the germ ideal {side}. -/\ndef {prefix}Gen{k:02d} ({args} : A) : A :=\n{body}\n"


def render_vector(name: str, prefix: str, side: str, count: int) -> str:
    rows = ",\n".join(f"    {prefix}Gen{k:02d} {ARGS}" for k in range(count))
    doc = f"The §k§-th generator of the germ ideal {side} (§k = 0, ..., {count - 1}§)."
    return f"/-- {doc} -/\ndef {name} ({ARGS} : A) : Fin {count} → A :=\n  ![\n{rows}]\n"


def render_def(name: str, prefix: str, side: str, polys: list[Poly]) -> str:
    gens = "\n".join(render_gen(prefix, side, k, p) for k, p in enumerate(polys))
    return gens + "\n" + render_vector(name, prefix, side, len(polys))


def lemma_blocks(flags: list[bool]) -> str:
    """One lemma per generator pair for Phi, for Phi after the flip and for the ring homomorphism, each checked by one
    call of ring or simp, so that no declaration needs more than the default heartbeat limit."""
    blocks = []
    for k, positive in enumerate(flags):
        n = f"{k:02d}"
        sign = "1" if positive else "-1"
        blocks.append(
            f"/-- Phi of generator §{k}§ of J_N- is §{sign}§ times generator §{k}§ of J_N+. -/\n"
            f"theorem jm_phi_gen{n} ({ARGS} : A) :\n"
            f"    jmGen{n} (-i) s1 s2 s3 (-s5) s4 s6 s8 s7 s9 =\n      ({sign} : A) * jpGen{n} {ARGS} := by\n"
            f"  unfold jmGen{n} jpGen{n}\n  ring\n\n"
            f"/-- Phi after the flip carries generator §{k}§ of J_N- to generator §{k}§ of J_N+. -/\n"
            f"theorem jm_phi_flip_gen{n} ({ARGS} : A) :\n"
            f"    jmGen{n} (-i) s1 s2 (-s3) (-s5) (-s4) (-s6) s8 s7 s9 =\n      jpGen{n} {ARGS} := by\n"
            f"  unfold jmGen{n} jpGen{n}\n  ring\n\n"
            f"/-- A ring homomorphism carries generator §{k}§ of J_N- at the ten variables to the one at their\n"
            f"images. -/\n"
            f"theorem map_jmGen{n} {{B : Type*}} [CommRing B] {{F : Type*}} [FunLike F A B] [RingHomClass F A B]\n"
            f"    (f : F) ({ARGS} : A) :\n"
            f"    f (jmGen{n} {ARGS}) =\n      jmGen{n} {' '.join('(f ' + v + ')' for v in base.VARS)} := by\n"
            f"  simp [jmGen{n}, map_ofNat f]\n"
        )
    return "\n".join(blocks).replace("§", "\x60") + "\n"


def theorems(count: int) -> str:
    args = "i s1 s2 s3 s4 s5 s6 s7 s8 s9"
    vs = " ".join(f"(v {n})" for n in range(10))
    phi = case_lines(count, lambda n: f"simpa [jm, jp, phiSign] using jm_phi_gen{n} {args}")
    flip = case_lines(count, lambda n: f"exact jm_phi_flip_gen{n} {args}")
    mapped = case_lines(count, lambda n: f"exact map_jmGen{n} f {vs}")
    return POSTAMBLE_THEOREMS.replace("@PHI@", phi).replace("@FLIP@", flip).replace("@MAP@", mapped).replace("§", "\x60")


def case_lines(count: int, tactic) -> str:
    return "\n".join(f"  · {tactic(f'{k:02d}')}" for k in range(count)) + "\n"


def source(minus: list[Poly], plus: list[Poly], flags: list[bool]) -> str:
    count = len(minus)
    negative = ", ".join(str(k) for k, f in enumerate(flags, start=1) if not f)
    sign_list = ", ".join("1" if f else "-1" for f in flags)
    return (
        PREAMBLE.replace("@COUNT@", str(count)).replace("@NEGATIVE@", negative)
        + render_def("jm", "jm", "J_N-", minus)
        + "\n"
        + render_def("jp", "jp", "J_N+", plus)
        + "\n"
        + "/-- The sign of the §k§-th generator pair: Phi of §jm k§ is §phiSign k§ times §jp k§. -/\n"
        + f"def phiSign : Fin {count} → ℤ :=\n  ![{sign_list}]\n"
        + POSTAMBLE
        + lemma_blocks(flags)
        + theorems(count)
    ).replace("§", "\x60")


PREAMBLE = """/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# The conjugation maps the germ ideal of N- onto the one of N+

Convention: §jm§ and §jp§ list the @COUNT@ generators of the ideals J_N- and J_N+ of the lines
§ideal J=§ of the E8-bar Rees scripts of gororoba-quantum, in the variables §i, s1, ..., s9§ with
integer coefficients, at index §k = 0, ..., 26§. §ci/quantum-sources/e8_conjugation_ideal_lean.py§
renders them from §conjugation_map.sing§ of gororoba-quantum, pinned by sha256;
§ci/quantum-sources/e8_conjugation_ideal.py§ renders the same lists into
§rocq/quantum/E8ConjugationIdeal.v§. The conjugation Phi is the substitution §i -> -i, s4 -> -s5,
s5 -> s4, s7 <-> s8§, every other variable fixed, so Phi of a generator §g i s1 ... s9§ is §g (-i)
s1 s2 s3 (-s5) s4 s6 s8 s7 s9§, and §phiVars§ is that vector of the ten variables. The flip
negates §s3, s5, s6§ (§flipVars§). Variable §0§ of §Fin 10§ is §i§ and variable §n§ is §s_n§.

## Main results

* §CayleyDickson.E8Conjugation.jm_phi§: over every commutative ring, Phi of generator §k§ of J_N-
  is §phiSign k§ times generator §k§ of J_N+; the sign is §-1§ at
  §k + 1 = @NEGATIVE@§ and §+1§ elsewhere.
* §CayleyDickson.E8Conjugation.jm_phi_flip§: Phi after the flip carries generator §k§ of J_N- to
  generator §k§ of J_N+ with no sign. The generator script checks in Python, outside Lean, that
  §phiSign k§ equals §(-1) ^ (deg s3 + deg s5 + deg s6)§ on every monomial of generator §k§; no
  Lean theorem states that parity character.
* §CayleyDickson.E8Conjugation.span_phi_jm§: in §MvPolynomial (Fin 10) R§ the ideal generated by
  the images of the generators of J_N- under the algebra endomorphism Phi is J_N+, and
  §span_phiFlip_jm§ states it for Phi after the flip.
-/

@[expose] public section

namespace CayleyDickson.E8Conjugation

variable {A : Type*} [CommRing A]

"""

POSTAMBLE = """
/-- The ten variables of a generator read from a vector: §0§ is §i§ and §n§ is §s_n§. -/
def jmAt (v : Fin 10 → A) : Fin 27 → A :=
  jm (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)

/-- The generators of J_N+ read from a vector of the ten variables. -/
def jpAt (v : Fin 10 → A) : Fin 27 → A :=
  jp (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)

/-- The vector of the variables after Phi: §i -> -i, s4 -> -s5, s5 -> s4, s7 <-> s8§. -/
def phiVars (v : Fin 10 → A) : Fin 10 → A :=
  ![-v 0, v 1, v 2, v 3, -v 5, v 4, v 6, v 8, v 7, v 9]

/-- The vector of the variables after the flip of §s3, s5, s6§. -/
def flipVars (v : Fin 10 → A) : Fin 10 → A :=
  ![v 0, v 1, v 2, -v 3, v 4, -v 5, -v 6, v 7, v 8, v 9]

/-- The sign of a generator pair is §1§ or §-1§, so it squares to §1§. -/
theorem phiSign_mul_self (k : Fin 27) : (phiSign k : A) * (phiSign k : A) = 1 := by
  fin_cases k <;> simp [phiSign]

"""

POSTAMBLE_THEOREMS = """/-- Phi of generator §k§ of J_N- is §phiSign k§ times generator §k§ of J_N+, by the lemma of each
pair. -/
theorem jm_phi (i s1 s2 s3 s4 s5 s6 s7 s8 s9 : A) (k : Fin 27) :
    jm (-i) s1 s2 s3 (-s5) s4 s6 s8 s7 s9 k =
      (phiSign k : A) * jp i s1 s2 s3 s4 s5 s6 s7 s8 s9 k := by
  fin_cases k
@PHI@
/-- Phi after the flip of §s3, s5, s6§ carries generator §k§ of J_N- to generator §k§ of J_N+ with
no sign. -/
theorem jm_phi_flip (i s1 s2 s3 s4 s5 s6 s7 s8 s9 : A) (k : Fin 27) :
    jm (-i) s1 s2 (-s3) (-s5) (-s4) (-s6) s8 s7 s9 k = jp i s1 s2 s3 s4 s5 s6 s7 s8 s9 k := by
  fin_cases k
@FLIP@
/-- A ring homomorphism carries the generators of J_N- at a vector to those at the image
vector. -/
theorem map_jmAt {B : Type*} [CommRing B] {F : Type*} [FunLike F A B] [RingHomClass F A B]
    (f : F) (v : Fin 10 → A) (k : Fin 27) : f (jmAt v k) = jmAt (fun n => f (v n)) k := by
  fin_cases k
@MAP@

section Polynomial

variable (R : Type*) [CommRing R]

/-- Generator §k§ of J_N- as a polynomial in the ten variables over §R§. -/
noncomputable def jmPoly (k : Fin 27) : MvPolynomial (Fin 10) R :=
  jmAt (fun n => MvPolynomial.X n) k

/-- Generator §k§ of J_N+ as a polynomial in the ten variables over §R§. -/
noncomputable def jpPoly (k : Fin 27) : MvPolynomial (Fin 10) R :=
  jpAt (fun n => MvPolynomial.X n) k

/-- The conjugation Phi as an algebra endomorphism of the polynomial ring. -/
noncomputable def phiMap : MvPolynomial (Fin 10) R →ₐ[R] MvPolynomial (Fin 10) R :=
  MvPolynomial.aeval (phiVars fun n => MvPolynomial.X n)

/-- The flip of §s3, s5, s6§ as an algebra endomorphism of the polynomial ring. -/
noncomputable def flipMap : MvPolynomial (Fin 10) R →ₐ[R] MvPolynomial (Fin 10) R :=
  MvPolynomial.aeval (flipVars fun n => MvPolynomial.X n)

/-- Phi after the flip. -/
noncomputable def phiFlipMap : MvPolynomial (Fin 10) R →ₐ[R] MvPolynomial (Fin 10) R :=
  (phiMap R).comp (flipMap R)

/-- Phi of a generator of J_N- is §phiSign k§ times the generator of J_N+, in the polynomial
ring. -/
theorem phiMap_jmPoly (k : Fin 27) :
    phiMap R (jmPoly R k) = (phiSign k : MvPolynomial (Fin 10) R) * jpPoly R k := by
  have h := jm_phi (MvPolynomial.X 0 : MvPolynomial (Fin 10) R) (MvPolynomial.X 1)
    (MvPolynomial.X 2) (MvPolynomial.X 3) (MvPolynomial.X 4) (MvPolynomial.X 5) (MvPolynomial.X 6)
    (MvPolynomial.X 7) (MvPolynomial.X 8) (MvPolynomial.X 9) k
  have hv : (fun n => phiMap R (MvPolynomial.X n)) = phiVars (fun n => MvPolynomial.X n) :=
    funext fun n => MvPolynomial.aeval_X _ n
  rw [jmPoly, map_jmAt, hv]
  exact h

/-- Phi after the flip maps a generator of J_N- to the generator of J_N+ with no sign. -/
theorem phiFlipMap_jmPoly (k : Fin 27) : phiFlipMap R (jmPoly R k) = jpPoly R k := by
  have h := jm_phi_flip (MvPolynomial.X 0 : MvPolynomial (Fin 10) R) (MvPolynomial.X 1)
    (MvPolynomial.X 2) (MvPolynomial.X 3) (MvPolynomial.X 4) (MvPolynomial.X 5) (MvPolynomial.X 6)
    (MvPolynomial.X 7) (MvPolynomial.X 8) (MvPolynomial.X 9) k
  have hv : (fun m => phiMap R (flipMap R (MvPolynomial.X m))) =
      (![-MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, -MvPolynomial.X 3,
        -MvPolynomial.X 5, -MvPolynomial.X 4, -MvPolynomial.X 6, MvPolynomial.X 8,
        MvPolynomial.X 7, MvPolynomial.X 9] : Fin 10 → MvPolynomial (Fin 10) R) := by
    funext m
    fin_cases m <;> simp [phiMap, flipMap, phiVars, flipVars]
  rw [jmPoly, phiFlipMap, AlgHom.comp_apply, map_jmAt, map_jmAt, hv]
  exact h

/-- Phi carries the ideal J_N- onto J_N+: the ideal generated by the images of the generators of
J_N- is the ideal generated by the generators of J_N+. -/
theorem span_phi_jm :
    Ideal.span (phiMap R '' Set.range (jmPoly R)) = Ideal.span (Set.range (jpPoly R)) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    rw [phiMap_jmPoly]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    have h : jpPoly R k = (phiSign k : MvPolynomial (Fin 10) R) * phiMap R (jmPoly R k) := by
      rw [phiMap_jmPoly, ← mul_assoc, phiSign_mul_self, one_mul]
    rw [SetLike.mem_coe, h]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, ⟨k, rfl⟩, rfl⟩)

/-- Phi after the flip carries the ideal J_N- onto J_N+. -/
theorem span_phiFlip_jm :
    Ideal.span (phiFlipMap R '' Set.range (jmPoly R)) = Ideal.span (Set.range (jpPoly R)) := by
  rw [← Set.range_comp]
  congr 2
  funext k
  exact phiFlipMap_jmPoly R k

end Polynomial

end CayleyDickson.E8Conjugation
"""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true", help="write the tracked Lean module")
    mode.add_argument("--check", action="store_true", help="compare the rendering with the tracked module")
    parser.add_argument("--source", help="with --check, the file to compare instead of the tracked module")
    arguments = parser.parse_args()
    if arguments.write and arguments.source:
        parser.error("--source applies to --check only")
    minus, plus = base.generator_lists()
    flags = base.signs(minus, plus)
    check_flip_character(minus, plus, flags)
    text = source(minus, plus, flags)
    target = TARGET
    if arguments.write:
        if TARGET.is_symlink() or not TARGET.parent.is_dir() or not TARGET.resolve().is_relative_to(MATH.resolve()):
            raise fail(f"{TARGET} is no plain file of this checkout")
        TARGET.write_text(text, encoding="utf-8")
        print(f"e8_conjugation_ideal_lean: wrote {TARGET.name}; {len(flags)} generator pairs, {flags.count(False)} with sign -1")
        return 0
    if arguments.source:
        target = Path(arguments.source)
    if not target.is_file() or target.read_text(encoding="utf-8") != text:
        print(f"e8_conjugation_ideal_lean: {target.name} differs from the rendering", file=sys.stderr)
        return 1
    print(f"e8_conjugation_ideal_lean: {target.name} fresh; {len(flags)} generator pairs, {flags.count(False)} with sign -1")
    return 0


if __name__ == "__main__":
    sys.exit(main())
