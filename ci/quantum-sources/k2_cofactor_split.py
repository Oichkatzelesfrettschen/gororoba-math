"""Render the split K2 cofactor certificate sources of rocq/quantum from the pinned certificate export.

The input is the a5-k2-cofactor-certificate-v1 file read by k2_cofactor_certificate.py. Eight quadrics are
certified through a basis change, q09 - 22069 q07, q21 - 22069 q17, q15 - q13, q18 - q13, q14 - q08,
q16 - q10, q11 - q08 and q13 - 16685 q06 in place of the quadric they start with (the cofactors are the same
linear combinations of the pinned cofactors modulo 32029), and every certified quadric is cut into steps.
A step holds the cofactors of a few J indices and a few outer Horner indices a (the products G_a H_a with
H_a the Horner sum over b >= a), at most about 600,000 monomial products of its identity, and the
remainders R_j and R_{j+1} of the chain R_0 = q(G), R_{j+1} = R_j - (the combination of the step j), which end
at R_m = 0. The outputs are K2CofactorE8barVBHeader.v (k2_J, k2_G and the 21 quadrics), K2CofactorE8barVBsNN_MM.v
(step MM of quadric NN: the check of K2CofactorSplit.v), K2CofactorE8barVBcNN.v (the chain of quadric NN and
the recovery of the original quadric), K2CofactorE8barVB.v (the statement for all 21 quadrics) and
K2Split.order (the compile order, one module name per line).

Usage: k2_cofactor_split.py INPUT.json --plan
       k2_cofactor_split.py INPUT.json --write [--step-products N]
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import k2_cofactor_certificate as base  # noqa: E402

P = base.PRIME
NV = base.NVARS
NJ = base.NJ
PAIRS = base.PAIRS
SLOT = 8
STEP_PRODUCTS = 600_000
CHUNK = 256
GENERATOR = "ci/quantum-sources/k2_cofactor_split.py"
OUTPUT_DIR = base.OUTPUT_DIR
# (quadric, base quadric, c): the certified polynomial is q - c q_base, in 1-based numbers.
BASIS = {9: (7, 22069), 21: (17, 22069), 15: (13, 1), 18: (13, 1), 14: (8, 1), 16: (10, 1), 11: (8, 1), 13: (6, 16685)}


def key(exps: list) -> int:
    return sum(e << (SLOT * i) for i, e in enumerate(exps))


def exps_of(k: int) -> list:
    return [(k >> (SLOT * i)) & 255 for i in range(NV)]


def to_dict(poly: list) -> dict:
    out: dict = {}
    for c, e in poly:
        k = key(e)
        out[k] = (out.get(k, 0) + c) % P
    return {k: c for k, c in out.items() if c}


def to_list(d: dict) -> list:
    return [[c, exps_of(k)] for k, c in sorted(d.items())]


def add_scaled(d: dict, s: dict, c: int) -> None:
    for k, v in s.items():
        w = (d.get(k, 0) + c * v) % P
        if w:
            d[k] = w
        else:
            d.pop(k, None)


def pmul(a: dict, b: dict) -> dict:
    out: dict = {}
    get = out.get
    for ka, ca in a.items():
        for kb, cb in b.items():
            k = ka + kb
            out[k] = get(k, 0) + ca * cb
    return {k: v % P for k, v in out.items() if v % P}


class Quadric:
    """The cofactors of one certified polynomial: a[k] (k < NJ), b[(i, a, b)], and the quadric terms."""

    def __init__(self, cert: dict, nn: int) -> None:
        self.nn = nn
        self.a: dict = {}
        self.b: dict = {}
        self.q = [tuple(t) for t in cert["quadrics"][nn - 1]["q"]]
        self.add(cert["quadrics"][nn - 1], 1)
        if nn in BASIS:
            other, c = BASIS[nn]
            self.add(cert["quadrics"][other - 1], -c % P)
            self.q += [((-c * t[0]) % P, t[1]) for t in cert["quadrics"][other - 1]["q"]]
            self.base = other
            self.c = c
        else:
            self.base = 0
            self.c = 0

    def add(self, quadric: dict, scale: int) -> None:
        for k, poly in quadric["a"]:
            d = self.a.setdefault(k, {})
            add_scaled(d, to_dict(poly), scale)
        for i, a, b, poly in quadric["b"]:
            d = self.b.setdefault((i, a, b), {})
            add_scaled(d, to_dict(poly), scale)

    def sparse(self, ks: list, aa: list) -> list:
        """Cofactor entries (generator index, polynomial list) of the J indices ks and Horner indices aa."""
        entries = [(k, to_list(self.a[k])) for k in ks if self.a.get(k)]
        for (i, a, b), d in sorted(self.b.items()):
            if a in aa and d:
                entries.append((NJ + i * PAIRS + base.pair_index(a, b), to_list(d)))
        return entries


def substitute(G: list, q: list) -> dict:
    total: dict = {}
    one = {0: 1}
    for c, e in q:
        term = one
        for a, ex in enumerate(e):
            for _ in range(ex):
                term = pmul(term, G[a])
        add_scaled(total, term, c % P)
    return total


def pieces_of(qd: Quadric, J: list, G: list) -> list:
    """The pieces of one certified polynomial: (kind, index, products, polynomial S)."""
    out = []
    for k in sorted(qd.a):
        if qd.a[k]:
            out.append(("a", k, len(qd.a[k]) * len(J[k]), pmul(qd.a[k], J[k])))
    for a in range(base.NY):
        products = 0
        H: dict = {}
        for b in range(a, base.NY):
            B: dict = {}
            for i in range(NV):
                poly = qd.b.get((i, a, b))
                if poly:
                    add_scaled(B, {k + (1 << (SLOT * i)): c for k, c in poly.items()}, 1)
            if B:
                products += len(G[b]) * len(B)
                add_scaled(H, pmul(G[b], B), 1)
        if H:
            products += len(G[a]) * len(H)
            out.append(("b", a, products, pmul(G[a], H)))
    return out


def group(pieces: list) -> list:
    steps: list = []
    cur: list = []
    count = 0
    for piece in pieces:
        if cur and count + piece[2] > STEP_PRODUCTS:
            steps.append(cur)
            cur, count = [], 0
        cur.append(piece)
        count += piece[2]
    if cur:
        steps.append(cur)
    return steps


def plan_quadric(cert: dict, nn: int, J: list, G: list) -> dict:
    qd = Quadric(cert, nn)
    steps = group(pieces_of(qd, J, G))
    R = substitute(G, qd.q)
    states = [R]
    maxexp = max([max(exps_of(k)) for k in R] + [0])
    for step in steps:
        R = dict(R)
        for piece in step:
            add_scaled(R, piece[3], -1)
        states.append(R)
        maxexp = max([maxexp] + [max(exps_of(k)) for k in R])
    if R:
        base.fail(f"quadric {nn}: the chain does not end at zero ({len(R)} terms left)")
    return {"qd": qd, "steps": steps, "states": states, "maxexp": maxexp}


def pack_poly(d: dict, slot_bits: int) -> str:
    items = sorted(d.items())
    term_bits = base.COEFFICIENT_BITS + slot_bits * NV
    chunks = []
    for start in range(0, len(items), CHUNK):
        word = 0
        part = items[start : start + CHUNK]
        for j, (k, c) in enumerate(part):
            ew = 0
            for e in reversed(exps_of(k)):
                ew = (ew << slot_bits) | e
            word |= (c | (ew << base.COEFFICIENT_BITS)) << (term_bits * j)
        chunks.append(f"    ({len(part)}%nat, 0x{word:x}%N)")
    return "[\n" + ";\n".join(chunks) + " ]" if chunks else "[]"


def sparse_text(entries: list) -> str:
    return "[\n" + ";\n".join(f"  ({k}%nat, {base.pack_chunks(poly)})" for k, poly in entries) + " ]"


def mod_name(nn: int, mm: int | None = None) -> str:
    return f"K2CofactorE8barVBs{nn:02d}_{mm:02d}" if mm is not None else f"K2CofactorE8barVBc{nn:02d}"


STEP_HEADER = r"""(** * Step {mm} of the split cofactor certificate of the K2 quadric {nn} of the fiber E8-bar to VB over F_32029.

    Generated by {generator} from the certificate with sha256 {digest}.

    Convention: K2CofactorSplit.v fixes [check_step_data] and [dec_polyw]. The step holds the cofactors of the
    J indices {ks} and of the Horner indices {aa}, indexed by the position of the generator in
    J ++ m_products 8 k2_G 2, and the remainder R_{mm1} as words of {sb}-bit exponent slots; the check
    states that R_{mm} - R_{mm1} is the combination of the step's cofactors. *)

From Stdlib Require Import ZArith List NArith.
Require Import HilbertCellCertificate K2CofactorCertificate K2CofactorFactored K2HilbertBound K2CofactorSplit
  K2CofactorE8barVBHeader{prev}.
Import ListNotations.
Open Scope Z_scope.
{quad}
Definition k2_R_{nn:02d}_{mm1} : poly :=
  {rdef}.

Definition k2_sp_{nn:02d}_{mm} : list (nat * list (nat * N)) :=
{sp}.

Lemma k2_check_{nn:02d}_{mm} :
  check_step_data 32029 8 k2_J k2_G (padd k2_R_{nn:02d}_{mm} (pneg k2_R_{nn:02d}_{mm1})) k2_sp_{nn:02d}_{mm} = true.
Proof. vm_compute. reflexivity. Qed.

Theorem k2_step_{nn:02d}_{mm} :
  LI 32029 8 (k2_J ++ m_products 8 k2_G 2) (padd k2_R_{nn:02d}_{mm} (pneg k2_R_{nn:02d}_{mm1})).
Proof. exact (check_step_data_sound _ _ _ _ _ _ k2_check_{nn:02d}_{mm}). Qed.
"""

QUAD_DEF = r"""
Definition k2_quad_{nn:02d} : list (Z * list nat) := {expr}.

Definition k2_R_{nn:02d}_0 : poly := subst_q 8 k2_G k2_quad_{nn:02d}.
"""

CHAIN = r"""(** * The K2 quadric {nn} of the fiber E8-bar to VB over F_32029 from its steps.

    Generated by {generator} from the certificate with sha256 {digest}.

    Convention: [LI_tele] of K2CofactorSplit.v adds a step to a proved remainder and [LI_recover] recovers a
    quadric from a certified combination q + d q' and the certified q'. Here the remainder R_0 is
    [subst_q 8 k2_G k2_quad_{nn:02d}], the chain has {m} step(s) and R_{m} is empty. *)

From Stdlib Require Import ZArith List NArith.
Require Import HilbertCellCertificate K2CofactorCertificate K2CofactorFactored K2HilbertBound K2CofactorSplit
  K2CofactorE8barVBHeader{imports}.
Import ListNotations.
Open Scope Z_scope.

Theorem k2_LIc_{nn:02d} :
  LI 32029 8 (k2_J ++ m_products 8 k2_G 2) (subst_q 8 k2_G k2_quad_{nn:02d}).
Proof.
{tele}
  apply LI_nil. exact prime_p32029.
Qed.
{recover}
Theorem k2_in_ideal_{nn:02d} :
  in_local_ideal 32029 8 (k2_J ++ m_products 8 k2_G 2) (subst_q 8 k2_G (nth {i} k2_quadrics [])).
Proof. exact (ili_of_LI _ _ _ _ k2_LI_{nn:02d}). Qed.

Print Assumptions k2_in_ideal_{nn:02d}.
"""


def quad_expr(nn: int) -> str:
    if nn in BASIS:
        other, c = BASIS[nn]
        return f"nth {nn - 1} k2_quadrics [] ++ qscale ({-c}) (nth {other - 1} k2_quadrics [])"
    return f"nth {nn - 1} k2_quadrics []"


def render_step(cert: dict, plan: dict, nn: int, mm: int) -> str:
    qd = plan["qd"]
    step = plan["steps"][mm]
    ks = [p[1] for p in step if p[0] == "a"]
    aa = [p[1] for p in step if p[0] == "b"]
    last = mm == len(plan["steps"]) - 1
    sb = 4 if plan["maxexp"] <= 15 else 8
    state = plan["states"][mm + 1]
    rdef = "[]" if last else f"dec_polyw 16 {sb} 8 {pack_poly(state, sb)}"
    return STEP_HEADER.format(
        mm=mm, mm1=mm + 1, nn=nn, generator=GENERATOR, digest=base.EXPECTED_SHA256, ks=ks or "none", aa=aa or "none",
        sb=sb, prev=(" " + mod_name(nn, mm - 1)) if mm else "", quad=QUAD_DEF.format(nn=nn, expr=quad_expr(nn)) if mm == 0 else "",
        rdef=rdef, sp=sparse_text(qd.sparse(ks, aa)),
    )


def render_chain(plan: dict, nn: int) -> str:
    m = len(plan["steps"])
    imports = "".join(" " + mod_name(nn, j) for j in range(m))
    tele = "\n".join(
        f"  apply (LI_tele 32029 8 _ k2_R_{nn:02d}_{j} k2_R_{nn:02d}_{j + 1} prime_p32029 k2_step_{nn:02d}_{j})." for j in range(m)
    )
    if nn in BASIS:
        other, c = BASIS[nn]
        imports += " " + mod_name(other)
        recover = (
            f"\nTheorem k2_LI_{nn:02d} :\n  LI 32029 8 (k2_J ++ m_products 8 k2_G 2) (subst_q 8 k2_G (nth {nn - 1} k2_quadrics [])).\n"
            f"Proof. exact (LI_recover 32029 8 _ k2_G (nth {nn - 1} k2_quadrics []) (nth {other - 1} k2_quadrics []) ({-c}) "
            f"prime_p32029 k2_LIc_{nn:02d} k2_LI_{other:02d}). Qed.\n"
        )
    else:
        recover = (
            f"\nTheorem k2_LI_{nn:02d} :\n  LI 32029 8 (k2_J ++ m_products 8 k2_G 2) (subst_q 8 k2_G (nth {nn - 1} k2_quadrics [])).\n"
            f"Proof. exact k2_LIc_{nn:02d}. Qed.\n"
        )
    return CHAIN.format(nn=nn, i=nn - 1, m=m, generator=GENERATOR, digest=base.EXPECTED_SHA256, imports=imports, tele=tele, recover=recover)


def quadric_order() -> list:
    order: list = []

    def visit(nn: int) -> None:
        if nn in order:
            return
        if nn in BASIS:
            visit(BASIS[nn][0])
        order.append(nn)

    for nn in range(1, base.NQUADRICS + 1):
        visit(nn)
    return order


def main() -> None:
    global STEP_PRODUCTS
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    actions = parser.add_mutually_exclusive_group(required=True)
    actions.add_argument("--plan", action="store_true", help="print the steps and remainder sizes")
    actions.add_argument("--write", action="store_true", help="write the Rocq sources")
    parser.add_argument("--step-products", type=int, default=STEP_PRODUCTS, help="product bound of one step")
    args = parser.parse_args()
    STEP_PRODUCTS = args.step_products
    cert = base.load(args.input)
    base.validate(cert)
    J = [to_dict(p) for p in cert["J"]]
    G = [to_dict(p) for p in cert["G"]]
    plans = {}
    for nn in quadric_order():
        plans[nn] = plan_quadric(cert, nn, J, G)
        pl = plans[nn]
        sizes = [len(s) for s in pl["states"]]
        prod = [sum(p[2] for p in s) for s in pl["steps"]]
        print(f"q{nn:02d} base={pl['qd'].base} maxexp={pl['maxexp']} steps={len(prod)} products={prod} remainder_terms={sizes}", flush=True)
    if args.plan:
        print("total products", sum(p[2] for pl in plans.values() for s in pl["steps"] for p in s), "pieces", sum(len(s) for pl in plans.values() for s in pl["steps"]))
        return
    order = ["K2CofactorE8barVBHeader"]
    (OUTPUT_DIR / "K2CofactorE8barVBHeader.v").write_text(base.render_header(cert), encoding="utf-8")
    for nn in quadric_order():
        pl = plans[nn]
        for mm in range(len(pl["steps"])):
            (OUTPUT_DIR / f"{mod_name(nn, mm)}.v").write_text(render_step(cert, pl, nn, mm), encoding="utf-8")
            order.append(mod_name(nn, mm))
        (OUTPUT_DIR / f"{mod_name(nn)}.v").write_text(render_chain(pl, nn), encoding="utf-8")
        order.append(mod_name(nn))
    imports = " ".join(mod_name(nn) for nn in range(1, base.NQUADRICS + 1))
    cases = "\n".join(f"  destruct i as [|i]; [exact k2_in_ideal_{i + 1:02d}|]." for i in range(base.NQUADRICS))
    (OUTPUT_DIR / "K2CofactorE8barVB.v").write_text(
        base.STATEMENT.format(digest=base.EXPECTED_SHA256, generator=GENERATOR, imports=imports, cases=cases), encoding="utf-8"
    )
    order.append("K2CofactorE8barVB")
    (OUTPUT_DIR / "K2Split.order").write_text("\n".join(order) + "\n", encoding="utf-8")
    print(f"wrote {len(order)} modules under {OUTPUT_DIR.relative_to(base.ROOT)}")


if __name__ == "__main__":
    main()
