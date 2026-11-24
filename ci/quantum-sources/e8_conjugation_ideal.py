"""Render rocq/quantum/E8ConjugationIdeal.v from the germ ideals J of the E8-bar Rees scripts of gororoba-quantum.

The input is docs/evidence/a5-exceptional-fibers/working/runs/e8-rees-fibers-v3-open-cells/conjugation/
conjugation_map.sing of the checkout GOROROBA_QUANTUM names, pinned by sha256, whose two lines that begin
"ideal J=" hold the 27 generators of J_N- and of J_N+ over Z[i, s1..s9]. The generator requires both literals
to equal those of the retained v2 Rees scripts e8-nm-p.v2-u-full.sing and e8-np-p.v2-u-full.sing (also pinned),
parses them as polynomials with i a free variable, applies the substitution Phi (i -> -i, s4 -> -s5, s5 -> s4,
s7 <-> s8) to each generator of J_N-, and requires the k-th image to equal plus or minus the k-th generator of
J_N+; the signs it finds enter the rendered source, whose proofs check every identity again with ring.

    GOROROBA_QUANTUM=PATH python3 -B ci/quantum-sources/e8_conjugation_ideal.py --check | --write

--check renders the source and compares it with rocq/quantum/E8ConjugationIdeal.v (status 1 on a difference);
--write writes it there. Standard library only.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import sys

from quantum_checkout import ROCQ, ROOT

RUNS = ROOT / "docs" / "evidence" / "a5-exceptional-fibers" / "working" / "runs"
CONJUGATION = RUNS / "e8-rees-fibers-v3-open-cells" / "conjugation" / "conjugation_map.sing"
V2_NM = RUNS / "e8-rees-fibers-v2-p32009" / "e8-nm-p.v2-u-full.sing"
V2_NP = RUNS / "e8-rees-fibers-v2-p32009" / "e8-np-p.v2-u-full.sing"
PINS = {
    CONJUGATION: "a1d7278b251e39c907641276ddee0d94919ffefa8613ad9863a2ff4e262d01ed",
    V2_NM: "4e88035959ed486dc7fe168dafcc97ca4314a0624616d039535bb071f6294cc2",
    V2_NP: "ee9318b04ec8dcb9e8c09858abc9eeb072da91235d5ac64ec0704633599c43ee",
}
TARGET = ROCQ / "E8ConjugationIdeal.v"
VARS = ("i", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9")
LITERAL = re.compile(r"ideal J=([^;]*);")
FACTOR = re.compile(r"^(i|s[1-9])(?:\^(\d+))?$")

Monomial = tuple[int, ...]
Poly = dict[Monomial, int]


def fail(message: str) -> SystemExit:
    print(f"e8_conjugation_ideal: {message}", file=sys.stderr)
    return SystemExit(1)


def read_pinned(path) -> str:
    if not path.is_file():
        raise fail(f"{path} does not exist")
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if digest != PINS[path]:
        raise fail(f"{path.name} has sha256 {digest}, pinned {PINS[path]}")
    return data.decode("utf-8")


def literals(text: str) -> list[str]:
    return [match.group(1) for match in LITERAL.finditer(text)]


def parse_term(term: str) -> tuple[Monomial, int]:
    coefficient = 1
    exponents = [0] * len(VARS)
    for factor in term.split("*"):
        if factor.isdigit():
            coefficient *= int(factor)
            continue
        match = FACTOR.match(factor)
        if match is None:
            raise fail(f"unparsed factor {factor!r}")
        exponents[VARS.index(match.group(1))] += int(match.group(2) or "1")
    return tuple(exponents), coefficient


def parse_poly(text: str) -> Poly:
    poly: Poly = {}
    body = text.replace(" ", "")
    for sign, term in re.findall(r"([+-]?)([^+-]+)", body):
        monomial, coefficient = parse_term(term)
        coefficient = -coefficient if sign == "-" else coefficient
        poly[monomial] = poly.get(monomial, 0) + coefficient
    return {m: c for m, c in poly.items() if c != 0}


def phi(poly: Poly) -> Poly:
    """i -> -i, s4 -> -s5, s5 -> s4, s7 <-> s8, every other variable fixed; i stays a free variable."""
    image: Poly = {}
    for e, c in poly.items():
        moved = (e[0], e[1], e[2], e[3], e[5], e[4], e[6], e[8], e[7], e[9])
        sign = -1 if (e[0] + e[4]) % 2 else 1
        image[moved] = image.get(moved, 0) + sign * c
    return {m: c for m, c in image.items() if c != 0}


def generator_lists() -> tuple[list[Poly], list[Poly]]:
    conjugation = literals(read_pinned(CONJUGATION))
    nm = literals(read_pinned(V2_NM))
    np = literals(read_pinned(V2_NP))
    if len(conjugation) != 2 or len(nm) != 1 or len(np) != 1:
        raise fail("expected two J literals in conjugation_map.sing and one in each v2 script")
    if conjugation[0] != nm[0] or conjugation[1] != np[0]:
        raise fail("the J literals of conjugation_map.sing differ from those of the v2 Rees scripts")
    minus = [parse_poly(g) for g in conjugation[0].split(",")]
    plus = [parse_poly(g) for g in conjugation[1].split(",")]
    if len(minus) != len(plus):
        raise fail(f"J_N- has {len(minus)} generators and J_N+ has {len(plus)}")
    return minus, plus


def signs(minus: list[Poly], plus: list[Poly]) -> list[bool]:
    out = []
    for k, (g, h) in enumerate(zip(minus, plus, strict=True), start=1):
        image = phi(g)
        if image == h:
            out.append(True)
        elif image == {m: -c for m, c in h.items()}:
            out.append(False)
        else:
            raise fail(f"Phi of generator {k} of J_N- is no sign multiple of generator {k} of J_N+")
    return out


def render_term(monomial: Monomial, coefficient: int) -> str:
    factors = [f"zc {abs(coefficient)}"] if abs(coefficient) != 1 else []
    for name, power in zip(VARS, monomial, strict=True):
        factors.extend([name] * power)
    body = " * ".join(factors) if factors else "rI"
    return f"- ({body})" if coefficient < 0 else body


def render_poly(poly: Poly) -> str:
    terms = [render_term(m, poly[m]) for m in sorted(poly, key=lambda m: (-sum(m), [-x for x in m]))]
    return " + ".join(terms)


def render_list(name: str, polys: list[Poly]) -> str:
    rows = ";\n    ".join(render_poly(p) for p in polys)
    return f"Definition {name} (i s1 s2 s3 s4 s5 s6 s7 s8 s9 : R) : list R :=\n  [ {rows} ].\n"


def source(minus: list[Poly], plus: list[Poly], flags: list[bool]) -> str:
    sign_list = "; ".join("true" if f else "false" for f in flags)
    negative = ", ".join(str(k) for k, f in enumerate(flags, start=1) if not f)
    return (
        PREAMBLE.replace("@COUNT@", str(len(minus))).replace("@NEGATIVE@", negative)
        + render_list("jm", minus)
        + "\n"
        + render_list("jp", plus)
        + f"\nDefinition phi_signs : list bool :=\n  [ {sign_list} ].\n"
        + POSTAMBLE
    )


PREAMBLE = """(** The conjugation Phi carries the germ ideal J of the E8-bar -> N- Rees scripts onto the one of N+.

    Convention. J_N- and J_N+ are the ideals generated by the @COUNT@ polynomials of the lines "ideal J=" of
    the E8-bar Rees scripts of gororoba-quantum (docs/evidence/a5-exceptional-fibers/working/runs/
    e8-rees-fibers-v2-p32009/e8-nm-p.v2-u-full.sing and e8-np-p.v2-u-full.sing, line 156 of the six v3 cell
    scripts of e8-rees-fibers-v3-open-cells, and conjugation/conjugation_map.sing there), in the variables
    i, s1, ..., s9 with integer coefficients; jm and jp list them in that order. The ideal generated by a list
    g is the set of linear combinations sum_k c_k g_k with coefficients c_k in the ring (gen_ideal).
    Phi is the substitution i -> -i, s4 -> -s5, s5 -> s4, s7 <-> s8, every other s_k fixed, so the image of
    a generator g(i, s) is g(-i, s1, s2, s3, -s5, s4, s6, s8, s7, s9). The source is rendered by
    ci/quantum-sources/e8_conjugation_ideal.py of gororoba-math from those files, pinned by sha256.

    Main results.
    - phi_generators: for every commutative ring R and all i, s1, ..., s9 in R, Phi of the k-th generator
      of J_N- equals the k-th generator of J_N+ times a sign; the sign is -1 at k = @NEGATIVE@ and +1
      elsewhere.
    - conjugation_ideal: hence Phi(J_N-) = J_N+ as ideals, and phi_in_plus and plus_in_phi state the two
      inclusions generator by generator.

    Scope. The identities hold with i a free variable: no generator holds a power of i above the first, and
    the substitution matches monomials one to one. So they hold in Z[i, s1..s9], and by base change in
    Q[i, s1..s9] / (i^2 + 1), the ring of ledger row A5-591 of gororoba-quantum, where Phi is a ring
    automorphism and Phi(J_N-) is the ideal generated by the images of the generators. Generators 13 and 16,
    and 23 and 26, coincide in each list.

    The 10 generators that the scalar comparison of conjugation_map.sing reports absent. That script replaces
    each list by its reduced standard basis for the degree reverse lexicographic order dp on
    (i, s1, ..., s9) before it compares (82 elements for J_N-, 80 for J_N+). Phi permutes s4 with s5 and s7
    with s8, which dp distinguishes, so the image of the reduced basis of J_N- generates J_N+ but is no
    standard basis of it for dp: 20 of the 80 leading monomials of the reduced basis of J_N+ lie outside the
    monomial ideal of the leading monomials of the 82 images, and the standard basis of the images is the
    80-element basis of J_N+ (Singular 4.4.1). After reduction modulo i^2 + 1 and normalization to leading
    coefficient 1, 72 of the 82 images are elements of that basis and 10 are not. The 10 are therefore
    elements of J_N+ that its reduced basis does not list, and the generator lists above correspond one to
    one with unit cofactors.

    The Rees scripts compute modulo a prime with i a root of -1, and replace J by the intersection of its
    minimal primes through the origin before the Rees stage; this file states the equality for the listed
    generators, before that replacement. *)

From Stdlib Require Import ZArith List Ring Ring_theory InitialRing.
Import ListNotations.

Declare Scope conj_scope.

Section ConjugationIdeal.

Variable R : Type.
Variables (rO rI : R) (radd rmul rsub : R -> R -> R) (ropp : R -> R).
Hypothesis Rth : ring_theory rO rI radd rmul rsub ropp (@eq R).
Add Ring conjugation_ring : Rth.

Local Notation "x + y" := (radd x y) : conj_scope.
Local Notation "x * y" := (rmul x y) : conj_scope.
Local Notation "- x" := (ropp x) : conj_scope.
Local Open Scope conj_scope.

(** zc n is the integer n in R, the image of the unique ring map from Z. *)
Definition zc (n : Z) : R := gen_phiZ rO rI radd rmul ropp n.

"""

POSTAMBLE = """
Definition sgn (e : bool) (x : R) : R := if e then x else - x.

Fixpoint signed (e : list bool) (g : list R) : list R :=
  match e, g with
  | b :: e', x :: g' => sgn b x :: signed e' g'
  | _, _ => g
  end.

Fixpoint lincomb (c g : list R) : R :=
  match c, g with
  | a :: c', x :: g' => a * x + lincomb c' g'
  | _, _ => rO
  end.

Definition gen_ideal (g : list R) (x : R) : Prop := exists c, lincomb c g = x.

(** A sign moves from a generator to its cofactor. *)
Lemma lincomb_signed : forall e c g, lincomb (signed e c) g = lincomb c (signed e g).
Proof.
  induction e as [| b e IH]; intros [| a c] [| x g]; cbn [signed lincomb]; try reflexivity.
  rewrite IH. destruct b; cbn [sgn]; ring.
Qed.

(** Signs are involutive. *)
Lemma signed_signed : forall e g, signed e (signed e g) = g.
Proof.
  induction e as [| b e IH]; intros [| x g]; cbn [signed]; try reflexivity.
  rewrite IH. destruct b; cbn [sgn]; [reflexivity | f_equal; ring].
Qed.

(** Changing the signs of generators leaves the generated ideal unchanged. *)
Lemma gen_ideal_signed : forall e g x, gen_ideal (signed e g) x <-> gen_ideal g x.
Proof.
  intros e g x. split; intros [c Hc]; exists (signed e c).
  - rewrite lincomb_signed. exact Hc.
  - rewrite lincomb_signed, signed_signed. exact Hc.
Qed.

(** Each generator lies in the ideal it generates, with a unit-vector cofactor. *)
Lemma gen_ideal_In : forall g y, In y g -> gen_ideal g y.
Proof.
  induction g as [| x g IH]; intros y Hy; [destruct Hy |].
  destruct Hy as [<- | Hy].
  - exists [rI]. cbn [lincomb]. ring.
  - destruct (IH y Hy) as [c Hc]. exists (rO :: c). cbn [lincomb]. rewrite Hc. ring.
Qed.

Lemma cons_eq : forall (a b : R) l l', a = b -> l = l' -> a :: l = b :: l'.
Proof. intros a b l l' -> ->. reflexivity. Qed.

(** Phi of the k-th generator of J_N- is the k-th generator of J_N+ up to sign, by ring on each pair. *)
Theorem phi_generators : forall i s1 s2 s3 s4 s5 s6 s7 s8 s9,
  jm (- i) s1 s2 s3 (- s5) s4 s6 s8 s7 s9 = signed phi_signs (jp i s1 s2 s3 s4 s5 s6 s7 s8 s9).
Proof.
  intros. unfold jm, jp, phi_signs. cbn [signed sgn].
  repeat (apply cons_eq; [ring |]). reflexivity.
Qed.

(** Phi(J_N-) = J_N+: the ideals generated by the images and by the generators of J_N+ coincide. *)
Theorem conjugation_ideal : forall i s1 s2 s3 s4 s5 s6 s7 s8 s9 x,
  gen_ideal (jm (- i) s1 s2 s3 (- s5) s4 s6 s8 s7 s9) x <-> gen_ideal (jp i s1 s2 s3 s4 s5 s6 s7 s8 s9) x.
Proof.
  intros. rewrite phi_generators. apply gen_ideal_signed.
Qed.

(** Every image Phi(g) of a generator of J_N- lies in J_N+. *)
Theorem phi_in_plus : forall i s1 s2 s3 s4 s5 s6 s7 s8 s9,
  Forall (gen_ideal (jp i s1 s2 s3 s4 s5 s6 s7 s8 s9)) (jm (- i) s1 s2 s3 (- s5) s4 s6 s8 s7 s9).
Proof.
  intros. apply Forall_forall. intros y Hy.
  apply conjugation_ideal, gen_ideal_In, Hy.
Qed.

(** Every generator of J_N+ lies in Phi(J_N-). *)
Theorem plus_in_phi : forall i s1 s2 s3 s4 s5 s6 s7 s8 s9,
  Forall (gen_ideal (jm (- i) s1 s2 s3 (- s5) s4 s6 s8 s7 s9)) (jp i s1 s2 s3 s4 s5 s6 s7 s8 s9).
Proof.
  intros. apply Forall_forall. intros y Hy.
  apply conjugation_ideal, gen_ideal_In, Hy.
Qed.

End ConjugationIdeal.

(** The integer instance, and the check that the conjugation i -> -i is needed: with i fixed, the first
    generator of J_N- under s4 -> -s5, s5 -> s4, s7 <-> s8 reads 8 s2 s8 + s5^2 + 8 i s7, against
    8 s2 s8 + s5^2 - 8 i s7 for J_N+; at i = s2 = s7 = s8 = 1 and every other s_k = 0 the two are 16 and 0. *)
Definition jm_Z := jm Z 0%Z 1%Z Z.add Z.mul Z.opp.
Definition jp_Z := jp Z 0%Z 1%Z Z.add Z.mul Z.opp.

Corollary conjugation_ideal_Z : forall i s1 s2 s3 s4 s5 s6 s7 s8 s9 x,
  gen_ideal Z 0%Z Z.add Z.mul (jm_Z (- i) s1 s2 s3 (- s5) s4 s6 s8 s7 s9)%Z x
  <-> gen_ideal Z 0%Z Z.add Z.mul (jp_Z i s1 s2 s3 s4 s5 s6 s7 s8 s9) x.
Proof. exact (conjugation_ideal Z 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Zth). Qed.

Lemma phi_needs_conjugation :
  hd 0%Z (jm_Z 1 0 1 0 0 0 0 1 1 0)%Z = 16%Z /\\ hd 0%Z (jp_Z 1 0 1 0 0 0 0 1 1 0)%Z = 0%Z.
Proof. vm_compute. split; reflexivity. Qed.

Print Assumptions conjugation_ideal.
Print Assumptions phi_in_plus.
Print Assumptions plus_in_phi.
"""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true", help="write rocq/quantum/E8ConjugationIdeal.v")
    mode.add_argument("--check", action="store_true", help="compare the rendering with the tracked source")
    arguments = parser.parse_args()
    minus, plus = generator_lists()
    flags = signs(minus, plus)
    text = source(minus, plus, flags)
    if arguments.write:
        TARGET.write_text(text, encoding="utf-8")
        print(
            f"e8_conjugation_ideal: wrote {TARGET.name}; "
            f"{len(flags)} generator pairs, {flags.count(False)} with sign -1"
        )
        return 0
    if not TARGET.is_file() or TARGET.read_text(encoding="utf-8") != text:
        print(f"e8_conjugation_ideal: {TARGET.name} differs from the rendering", file=sys.stderr)
        return 1
    print(f"e8_conjugation_ideal: {TARGET.name} fresh; {len(flags)} generator pairs, {flags.count(False)} with sign -1")
    return 0


if __name__ == "__main__":
    sys.exit(main())
