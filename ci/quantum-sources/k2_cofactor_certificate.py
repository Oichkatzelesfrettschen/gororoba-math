"""Render the K2 cofactor certificate sources of rocq/quantum from the pinned certificate export.

The input is the a5-k2-cofactor-certificate-v1 file of the fiber E8-bar to VB over F_32029 (21 quadrics q of
the K2 relations, each with u = 1 and cofactors a_k of the 17 generators J_k and b_{i,ab} of the products
t_i G_a G_b). Only the file with the pinned sha256 is accepted. The outputs are K2CofactorE8barVBHeader.v
(the J and G tables of the canonical header and the 21 quadrics), one K2CofactorE8barVBqNN.v per quadric
(the cofactors packed into numbers, and the proof that check_data of K2CofactorCertificate.v accepts them)
and K2CofactorE8barVB.v (the statement for all 21 quadrics).

Usage: k2_cofactor_certificate.py INPUT.json --write
       k2_cofactor_certificate.py INPUT.json --check
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

EXPECTED_SHA256 = "2d330081a19eb2e21dcc615185ace7b4f9e946597d6acde591786be2c5324c6f"
HEADER_SHA256 = "6b3cea4923b4e0e2650349e64a83f902fcbbbe288ba364c685a552b03f9e82e0"
SCHEMA = "a5-k2-cofactor-certificate-v1"
GENERATOR = "ci/quantum-sources/k2_cofactor_certificate.py"
ROOT = Path(__file__).resolve().parents[2]
OUTPUT_DIR = ROOT / "rocq" / "quantum"
PRIME = 32029
NVARS = 8
NY = 10
NJ = 17
PAIRS = NY * (NY + 1) // 2
NQUADRICS = 21
COEFFICIENT_BITS = 16
SLOT_BITS = COEFFICIENT_BITS + 4 * NVARS
CHUNK_TERMS = 256
TERMS_PER_LINE = 2


def fail(message: str) -> None:
    sys.exit(f"k2_cofactor_certificate: {message}")


def load(path: Path) -> dict:
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if digest != EXPECTED_SHA256:
        fail(f"input sha256 {digest} is not the pinned {EXPECTED_SHA256}")
    return json.loads(data)


def check_term(term: list, nvars: int, limit_exponent: int = 15) -> None:
    coefficient, exponents = term
    if not 0 <= coefficient < PRIME or len(exponents) != nvars:
        fail("malformed term")
    if any(not 0 <= e <= limit_exponent for e in exponents):
        fail("exponent outside the four-bit slot")


def validate(cert: dict) -> None:
    if cert.get("schema") != SCHEMA or cert.get("prime") != PRIME:
        fail("unexpected schema or prime")
    if cert["header"]["sha256"] != HEADER_SHA256:
        fail("unexpected header digest")
    if len(cert["vars"]["s"]) != NVARS or len(cert["vars"]["y"]) != NY:
        fail("unexpected variable counts")
    if len(cert["J"]) != NJ or len(cert["G"]) != NY or len(cert["quadrics"]) != NQUADRICS:
        fail("unexpected table sizes")
    form = cert["form"]
    if form["kind"] != "global" or form["truncation_N"] is not None or form["pair_order"] != "a <= b":
        fail("the identity is not the global one over pairs a <= b")
    for table in ("J", "G"):
        for poly in cert[table]:
            for term in poly:
                check_term(term, NVARS)
    for quadric in cert["quadrics"]:
        if quadric["u"] != [[1, [0] * NVARS]]:
            fail("a unit u differs from 1")
        for coefficient, exponents in quadric["q"]:
            if not 0 <= coefficient < PRIME or len(exponents) != NY or sum(exponents) != 2:
                fail("a quadric term is malformed")
        for k, poly in quadric["a"]:
            if not 0 <= k < NJ:
                fail("a J index is out of range")
            for term in poly:
                check_term(term, NVARS)
        for i, a, b, poly in quadric["b"]:
            if not (0 <= i < NVARS and 0 <= a <= b < NY):
                fail("a b index is out of range")
            for term in poly:
                check_term(term, NVARS)


def pair_index(a: int, b: int) -> int:
    """Position of the product G_a G_b in the msets order of HilbertCellCertificate.v."""
    return sum(NY - x for x in range(a)) + (b - a)


def sparse_cofactors(quadric: dict) -> list[tuple[int, list]]:
    entries = [(k, poly) for k, poly in quadric["a"] if poly]
    entries += [(NJ + i * PAIRS + pair_index(a, b), poly) for i, a, b, poly in quadric["b"] if poly]
    indices = [index for index, _ in entries]
    if len(set(indices)) != len(indices):
        fail("two cofactor entries share a generator index")
    return entries


def term_m8(term: list) -> str:
    coefficient, exponents = term
    return f"(m8 {' '.join(str(x) for x in exponents)}, {coefficient})"


def poly_block(poly: list) -> str:
    terms = [term_m8(t) for t in poly]
    lines = ["    " + "; ".join(terms[i : i + TERMS_PER_LINE]) for i in range(0, len(terms), TERMS_PER_LINE)]
    return "  [\n" + ";\n".join(lines) + " ]"


def quadric_text(q: list) -> str:
    return "[ " + "; ".join(f"(qt {c} {' '.join(str(x) for x in e)})" for c, e in q) + " ]"


def pack_chunks(poly: list) -> str:
    out = []
    for start in range(0, len(poly), CHUNK_TERMS):
        part = poly[start : start + CHUNK_TERMS]
        word = 0
        for j, (coefficient, exponents) in enumerate(part):
            exponent_word = 0
            for e in reversed(exponents):
                exponent_word = exponent_word * 16 + e
            word |= (coefficient | (exponent_word << COEFFICIENT_BITS)) << (SLOT_BITS * j)
        out.append(f"    ({len(part)}%nat, 0x{word:x}%N)")
    return "[\n" + ";\n".join(out) + " ]"


def data_text(quadric: dict) -> str:
    cofactors = ";\n".join(f"  ({k}%nat, {pack_chunks(poly)})" for k, poly in sparse_cofactors(quadric))
    return f"mk_kdata {pack_chunks(quadric['u'])}\n  [\n{cofactors} ]"


def render_header(cert: dict) -> str:
    j_body = ";\n".join(poly_block(p) for p in cert["J"])
    g_body = ";\n".join(poly_block(p) for p in cert["G"])
    q_body = ";\n".join("  " + quadric_text(qd["q"]) for qd in cert["quadrics"])
    return HEADER.format(
        digest=EXPECTED_SHA256, generator=GENERATOR, j_body=j_body, g_body=g_body, q_body=q_body
    )


def render_quadric(cert: dict, i: int) -> str:
    nn = f"{i + 1:02d}"
    return QUADRIC.format(
        i=i, n1=i + 1, nn=nn, digest=EXPECTED_SHA256, generator=GENERATOR, data=data_text(cert["quadrics"][i])
    )


def render_statement() -> str:
    imports = " ".join(f"K2CofactorE8barVBq{i + 1:02d}" for i in range(NQUADRICS))
    cases = "\n".join(
        f"  destruct i as [|i]; [exact k2_in_ideal_{i + 1:02d}|]." for i in range(NQUADRICS)
    )
    return STATEMENT.format(digest=EXPECTED_SHA256, generator=GENERATOR, imports=imports, cases=cases)


def render_all(cert: dict) -> dict[str, str]:
    validate(cert)
    files = {"K2CofactorE8barVBHeader.v": render_header(cert)}
    for i in range(NQUADRICS):
        files[f"K2CofactorE8barVBq{i + 1:02d}.v"] = render_quadric(cert, i)
    files["K2CofactorE8barVB.v"] = render_statement()
    return files


HEADER = r"""(** * The cofactor certificate data of the K2 relations of the fiber E8-bar to VB over F_32029.

    Generated by {generator} from the certificate with sha256 {digest}.

    Convention: K2CofactorCertificate.v fixes the statement ([in_local_ideal] of [subst_q]) and the checker.
    The tables below are the 17 polynomials J and the 10 polynomials G of the canonical header in 8
    variables, each term a (monomial, coefficient) pair with the exponent vector written by [m8], and the
    21 quadrics of the K2 relations, each a list of (coefficient, exponent vector of y_1 .. y_10) pairs
    written by [qt]. *)

From Stdlib Require Import ZArith List.
Require Import HilbertCellCertificate K2CofactorCertificate.
Import ListNotations.
Open Scope Z_scope.

Definition m8 (a b c d e f g h : nat) : mono := [a; b; c; d; e; f; g; h].

Definition k2_J : list poly :=
[
{j_body} ].

Definition k2_G : list poly :=
[
{g_body} ].

Definition qt (c : Z) (a b c' d e f g h i j : nat) : Z * list nat :=
  (c, [a; b; c'; d; e; f; g; h; i; j]).

Definition k2_quadrics : list (list (Z * list nat)) :=
[
{q_body} ].
"""

QUADRIC = r"""(** * The cofactor certificate of the K2 quadric {n1} of the fiber E8-bar to VB over F_32029.

    Generated by {generator} from the certificate with sha256 {digest}.

    Convention: [decode_cert] of K2CofactorCertificate.v reads each chunk (k, w) as k terms of 48 bits, the
    coefficient in the low 16 bits and the exponents of t_1 .. t_8 above them in four bits each. The
    cofactor entries are indexed by the position of the generator in J ++ m_products 8 k2_G 2. *)

From Stdlib Require Import ZArith List NArith.
Require Import HilbertCellCertificate K2CofactorCertificate K2CofactorE8barVBHeader.
Import ListNotations.
Open Scope Z_scope.

Definition k2_data_{nn} : kdata :=
{data}.

Lemma k2_check_{nn} :
  check_data 32029 8 k2_J k2_G 2 (nth {i} k2_quadrics []) 16 k2_data_{nn} = true.
Proof. vm_compute. reflexivity. Qed.

Theorem k2_in_ideal_{nn} :
  in_local_ideal 32029 8 (k2_J ++ m_products 8 k2_G 2) (subst_q 8 k2_G (nth {i} k2_quadrics [])).
Proof. exact (check_data_sound _ _ _ _ _ _ _ _ k2_check_{nn}). Qed.

Print Assumptions k2_in_ideal_{nn}.
"""

STATEMENT = r"""(** * The 21 quadrics of the K2 relations lie in J + m (G)^2 for the fiber E8-bar to VB over F_32029.

    Generated by {generator} from the certificate with sha256 {digest}.

    Convention: [subst_q 8 k2_G q] is the polynomial in t_1 .. t_8 that replaces y_a by the generator G_a,
    and [in_local_ideal] of HilbertCellCertificate.v states membership in the local ideal of
    J ++ m_products 8 k2_G 2, the ideal of J plus t_k times each product G_a G_b with a <= b. The
    membership places each quadric in the kernel of the map from the polynomial ring in y_1 .. y_10 to
    the degree-2 piece of the fiber cone P_2 / (m P_2 + J). *)

From Stdlib Require Import ZArith List Lia.
Require Import HilbertCellCertificate K2CofactorCertificate K2CofactorE8barVBHeader {imports}.
Import ListNotations.
Open Scope Z_scope.

Theorem k2_quadrics_in_ideal : forall i, (i < {nq})%nat ->
  in_local_ideal 32029 8 (k2_J ++ m_products 8 k2_G 2) (subst_q 8 k2_G (nth i k2_quadrics [])).
Proof.
  intros i Hi.
{cases}
  lia.
Qed.

Print Assumptions k2_quadrics_in_ideal.
"""
STATEMENT = STATEMENT.replace("{nq}", str(NQUADRICS))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="the pinned cofactor certificate JSON")
    actions = parser.add_mutually_exclusive_group(required=True)
    actions.add_argument("--write", action="store_true", help="write the Rocq sources")
    actions.add_argument("--check", action="store_true", help="require the tracked sources to equal the rendering")
    args = parser.parse_args()
    files = render_all(load(args.input))
    if args.write:
        for name, text in files.items():
            (OUTPUT_DIR / name).write_text(text, encoding="utf-8")
        print(f"wrote {len(files)} files under {OUTPUT_DIR.relative_to(ROOT)}")
        return
    for name, text in files.items():
        path = OUTPUT_DIR / name
        if not path.is_file() or path.read_text(encoding="utf-8") != text:
            fail(f"{path.relative_to(ROOT)} differs from the rendering")
    print("ok")


if __name__ == "__main__":
    main()
