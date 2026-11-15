"""Integer kernel certificates of left multiplication at the canonical points of the A_5 nullity strata.

A point is a doubly pure element y of the 32-dimensional Cayley-Dickson algebra with integer coordinates, read
from the split coordinates z'_1..z'_15 of docs/evidence/a5-strata-regularity/strata_regularity.py (REPS) by
z_k = i^popcount(k) z'_k, y_k = Re z_k, y_(16+k) = Im z_k. L is the 32 x 32 integer matrix of z -> y z in the
cd_core basis: column q is y e_q, entry (p xor q, q) = y_p cd_sign(32, p, q).

A certificate of the kernel of L is (d, P, V, C) over the integers with

    L V = 0,    d I = P L + V C,    C V = d I_n,

where V is 32 x n, C is n x 32 and P is 32 x 32. It gives nullity n over every field whose characteristic does
not divide d: the columns of V span the kernel and are independent. rocq/quantum/CdTowerCanonicalKernels.v states the
same three identities for the pair-tower product and proves them by vm_compute; this script produces the
certificate, checks it with cd_core and renders the Rocq file from it.

--generate computes each certificate from a unimodular diagonalization U L W = D of L (d is the least common
multiple of the nonzero diagonal entries, V the last n columns of W reduced by LLL, C = d times the last n rows of
the inverse of W, P = W (d / D) U), checks every certificate as --check does, and then writes certificates.json
and the Rocq file; a failed check leaves both files as they were. It needs python-flint.
--check reads certificates.json, recomputes y and L from the strata representatives and cd_core, verifies the
three identities and the rank in exact integer arithmetic, and requires the Rocq file to be the rendering of the
JSON; it uses python-flint only for the independent rank and Smith invariants.

Usage:
    GOROROBA_QUANTUM=PATH "$PYTHON" -B -W error ci/quantum-sources/kernel_certificates.py --check
    GOROROBA_QUANTUM=PATH "$PYTHON" -B -W error ci/quantum-sources/kernel_certificates.py --generate
"""

from __future__ import annotations

import argparse
import json
import math
import os
import re
import sys
from pathlib import Path
from typing import Any

import quantum_checkout

HERE = Path(__file__).resolve().parent
ROOT = quantum_checkout.ROOT
sys.path.insert(0, str(ROOT / "gororoba_quantum"))
sys.path.insert(0, str(ROOT / "docs/evidence/a5-strata-regularity"))

import cd_core  # noqa: E402
import parallel  # noqa: E402

CERTIFICATES = HERE / "certificates.json"
ROCQ_FILE = quantum_checkout.ROCQ / "CdTowerCanonicalKernels.v"
DIM = 32
NULLITY = {"W8": 8, "Ehat": 8, "Iso": 8, "Xp": 8, "Xm": 8, "B9": 12, "V": 12, "VB": 12, "Vap": 12, "Vam": 12,
           "Np": 16, "Nm": 16}  # fmt: skip
I_POWERS = ((1, 0), (0, 1), (-1, 0), (0, -1))
Matrix = list[list[int]]


def representatives() -> dict[str, list[int]]:
    """The split coordinates of one point of each orbit, from the strata regularity script."""
    import strata_regularity

    return {name: list(strata_regularity.REPS[name]) for name in NULLITY}


def point(split: list[int]) -> list[int]:
    """The 32 integer coordinates of y for split coordinates z'_1..z'_15."""
    y = [0] * DIM
    for k in range(1, 16):
        re, im = I_POWERS[k.bit_count() % 4]
        y[k] = re * split[k - 1]
        y[16 + k] = im * split[k - 1]
    return y


def left_matrix(y: list[int]) -> Matrix:
    rows = [[0] * DIM for _ in range(DIM)]
    for p, coefficient in enumerate(y):
        if coefficient:
            for q in range(DIM):
                rows[p ^ q][q] += coefficient * cd_core.cd_sign(DIM, p, q)
    return rows


def identity(n: int) -> Matrix:
    return [[int(i == j) for j in range(n)] for i in range(n)]


def product(a: Matrix, b: Matrix) -> Matrix:
    columns = list(zip(*b, strict=True)) if b else []
    return [[sum(x * y for x, y in zip(row, column, strict=True)) for column in columns] for row in a]


def transpose(a: Matrix) -> Matrix:
    return [list(column) for column in zip(*a, strict=True)]


def diagonalize(matrix: Matrix) -> tuple[Matrix, Matrix, Matrix, Matrix]:
    """Unimodular U, W and the inverse of W with U matrix W diagonal, by integer row and column operations."""
    a = [row[:] for row in matrix]
    size = len(a)
    u, w, w_inverse = identity(size), identity(size), identity(size)

    def swap_rows(i: int, j: int) -> None:
        a[i], a[j] = a[j], a[i]
        u[i], u[j] = u[j], u[i]

    def swap_columns(i: int, j: int) -> None:
        for row in a:
            row[i], row[j] = row[j], row[i]
        for row in w:
            row[i], row[j] = row[j], row[i]
        w_inverse[i], w_inverse[j] = w_inverse[j], w_inverse[i]

    for t in range(size):
        while True:
            entries = [(abs(a[i][j]), i, j) for i in range(t, size) for j in range(t, size) if a[i][j]]
            if not entries:
                return u, w, w_inverse, a
            _, i, j = min(entries)
            swap_rows(t, i)
            swap_columns(t, j)
            pivot = a[t][t]
            for i in range(t + 1, size):
                q = a[i][t] // pivot
                if q:
                    a[i] = [x - q * z for x, z in zip(a[i], a[t], strict=True)]
                    u[i] = [x - q * z for x, z in zip(u[i], u[t], strict=True)]
            for j in range(t + 1, size):
                q = a[t][j] // pivot
                if q:
                    for row in a:
                        row[j] -= q * row[t]
                    for row in w:
                        row[j] -= q * row[t]
                    w_inverse[t] = [x + q * z for x, z in zip(w_inverse[t], w_inverse[j], strict=True)]
            if not any(a[i][t] for i in range(t + 1, size)) and not any(a[t][j] for j in range(t + 1, size)):
                break
    return u, w, w_inverse, a


def certificate(item: tuple[str, list[int]]) -> dict[str, Any]:
    """The certificate of one point, from a diagonalization of L and an LLL reduction of the kernel basis."""
    from flint import fmpz_mat

    name, split = item
    y = point(split)
    left = left_matrix(y)
    u, w, w_inverse, diagonal = diagonalize(left)
    entries = [abs(diagonal[i][i]) for i in range(DIM)]
    rank = sum(1 for x in entries if x)
    if any(entries[i] == 0 for i in range(rank)) or any(entries[i] for i in range(rank, DIM)):
        raise ValueError(f"{name}: the diagonal form does not list its nonzero entries first")
    scalar = math.lcm(*entries[:rank])
    signs = [1 if diagonal[i][i] > 0 else -1 for i in range(rank)]
    pseudo = [
        [signs[i] * (scalar // entries[i]) * int(i == j) if i < rank else 0 for j in range(DIM)] for i in range(DIM)
    ]
    back = product(product(w, pseudo), u)
    kernel_rows = [[w[i][j] for i in range(DIM)] for j in range(rank, DIM)]
    reduced, change = fmpz_mat(kernel_rows).lll(True)
    change_rows = [[int(change[i, j]) for j in range(DIM - rank)] for i in range(DIM - rank)]
    inverse_change = fmpz_mat(change_rows).inv()
    vectors = [[int(reduced[i, j]) for j in range(DIM)] for i in range(DIM - rank)]
    lower = [[scalar * x for x in w_inverse[i]] for i in range(rank, DIM)]
    inverse_transpose = [[int(inverse_change[j, i].p) for j in range(DIM - rank)] for i in range(DIM - rank)]
    functionals = product(inverse_transpose, lower)
    return {"name": name, "split": split, "point": y, "scalar": scalar, "nullity": DIM - rank,
            "vectors": vectors, "functionals": functionals, "back": transpose(back)}  # fmt: skip


def defects(record: dict[str, Any], y: list[int]) -> list[str]:
    """The identities of the certificate that fail for the point y, in exact integer arithmetic."""
    out = []
    left = left_matrix(y)
    vectors = transpose(record["vectors"])
    functionals: Matrix = record["functionals"]
    back = transpose(record["back"])
    scalar: int = record["scalar"]
    nullity: int = record["nullity"]
    if len(vectors[0]) != nullity or len(functionals) != nullity:
        out.append("shape")
    if any(any(row) for row in product(left, vectors)):
        out.append("L V = 0")
    split = [
        [p + q for p, q in zip(r, s, strict=True)]
        for r, s in zip(product(back, left), product(vectors, functionals), strict=True)
    ]
    if split != [[scalar * int(i == j) for j in range(DIM)] for i in range(DIM)]:
        out.append("d I = P L + V C")
    if product(functionals, vectors) != [[scalar * int(i == j) for j in range(nullity)] for i in range(nullity)]:
        out.append("C V = d I")
    return out


def checked(item: tuple[dict[str, Any], list[int]]) -> dict[str, Any]:
    """Defects of one record against its strata representative, with flint's rank and Smith invariants of L."""
    from flint import fmpz_mat

    record, split = item
    y = point(split)
    problems = defects(record, y)
    if record["split"] != split or record["point"] != y:
        problems.append("point")
    left = fmpz_mat(left_matrix(y))
    smith = left.snf()
    invariants = [int(smith[i, i]) for i in range(DIM) if smith[i, i]]
    if DIM - left.rank() != record["nullity"] or record["nullity"] != NULLITY[str(record["name"])]:
        problems.append("nullity")
    if max(invariants) != record["scalar"]:
        problems.append("scalar is not the largest Smith invariant")
    return {"name": record["name"], "nullity": record["nullity"], "scalar": record["scalar"], "defects": problems,
            "invariants": {str(v): invariants.count(v) for v in sorted(set(invariants))}}  # fmt: skip


def rocq_list(values: list[int]) -> str:
    return "[" + "; ".join(str(v) if v >= 0 else f"({v})" for v in values) + "]"


def rocq_table(rows: list[list[int]]) -> str:
    return "[" + ";\n     ".join(rocq_list(row) for row in rows) + "]"


def render(records: list[dict[str, Any]]) -> str:
    """The Rocq file of the certificates; a deterministic function of the JSON records."""
    out = [
        "(** Kernels of left multiplication at the canonical points of the A_5 nullity strata.",
        "",
        "    Generated by docs/evidence/cd-tower-kernel-certificates/kernel_certificates.py from certificates.json;",
        "    edit the generator, not this file. Each point y is an element of level 5 with integer coordinates. For",
        "    each one, three finite checks over Z by vm_compute (the vectors are annihilated, the splitting",
        "    d z = back(y z) + sum_j f_j(z) v_j on the 32 basis vectors, and the duality f_j(v_l) = d delta_jl) give,",
        "    through CdTowerKernelCertificate.v, the kernel of z -> y z over every commutative ring D: it contains the",
        "    n vectors, d times each of its elements is a combination of them, and where the image of d in D is",
        "    invertible it is the free module on them. *)",
        "",
        "From Stdlib Require Import ZArith List Lia PeanoNat Ring Zmod.",
        "Require Import CdTowerRing CdTowerRingBasis CdTowerRingBaseChange CdTowerKernelCertificate.",
        "Import ListNotations.",
        "",
        "Module CanonicalKernels (D : CommutativeRing).",
        "Module H := IntegerHom D.",
        "Module KC := KernelCertificate IntegerRing D H.",
        "Import KC KC.BC.",
        "Local Open Scope Z_scope.",
        "",
        "(** The element of level k with the coordinates of a list, first half first. *)",
        "Fixpoint of_list (k : nat) (l : list Z) : TA.cd k :=",
        "  match k with",
        "  | O => hd 0 l",
        "  | S j => (of_list j (firstn (Nat.pow 2 j) l), of_list j (skipn (Nat.pow 2 j) l))",
        "  end.",
        "",
        "Definition row (table : list (list Z)) (j : nat) : TA.cd 5 := of_list 5 (nth j table []).",
        "",
        'Tactic Notation "below" integer(bound) tactic3(run) :=',
        '  let j := fresh "j" in let Hj := fresh "Hj" in',
        "  intros j Hj; do bound (destruct j as [|j]; [run |]); exfalso; lia.",
        "",
    ]
    for record in records:
        name, n, d = record["name"], record["nullity"], record["scalar"]
        out += [
            f"(** {name}: split coordinates {record['split']}, nullity {n}, d = {d}. *)",
            f"Definition {name}_point : TA.cd 5 := of_list 5 {rocq_list(record['point'])}.",
            f"Definition {name}_vectors : nat -> TA.cd 5 := row\n    {rocq_table(record['vectors'])}.",
            f"Definition {name}_functionals : nat -> TA.cd 5 := row\n    {rocq_table(record['functionals'])}.",
            f"Definition {name}_back : nat -> TA.cd 5 := row\n    {rocq_table(record['back'])}.",
            "",
            f"Lemma {name}_vectors_annihilated : forall j, (j < {n})%nat ->",
            f"  TA.mul 5 {name}_point ({name}_vectors j) = TA.zero 5.",
            f"Proof. below {n} (vm_compute; reflexivity). Qed.",
            "",
            f"Lemma {name}_splitting_on_basis : forall i, (i < Nat.pow 2 5)%nat ->",
            f"  TA.scale 5 {d} (SA.basis 5 i) =",
            f"  TA.add 5 (source_map 5 {name}_back (TA.mul 5 {name}_point (SA.basis 5 i)))",
            f"           (source_comb 5 {n} {name}_functionals {name}_vectors (SA.basis 5 i)).",
            "Proof. change (Nat.pow 2 5) with 32%nat. below 32 (vm_compute; reflexivity). Qed.",
            "",
            f"Lemma {name}_functionals_dual : forall j l, (j < {n})%nat -> (l < {n})%nat ->",
            f"  source_pair 5 ({name}_functionals j) ({name}_vectors l) = if Nat.eqb j l then {d} else 0.",
            "Proof.",
            f"  intros j l Hj Hl. revert l Hl. do {n} (destruct j as [|j]; [below {n} (vm_compute; reflexivity) |]).",
            "  exfalso; lia.",
            "Qed.",
            "",
            f"Theorem {name}_kernel_vectors : forall j, (j < {n})%nat ->",
            f"  TB.mul 5 (tmap 5 {name}_point) (tmap 5 ({name}_vectors j)) = TB.zero 5.",
            f"Proof. exact (kernel_vectors 5 {n} {name}_point {name}_vectors {name}_vectors_annihilated). Qed.",
            "",
            f"Theorem {name}_kernel_spanned : forall z, TB.mul 5 (tmap 5 {name}_point) z = TB.zero 5 ->",
            f"  TB.scale 5 (H.h {d}) z = target_comb 5 {n} {name}_functionals {name}_vectors z.",
            "Proof.",
            f"  exact (kernel_spanned 5 {n} {name}_point {d} {name}_back {name}_functionals {name}_vectors",
            f"           {name}_splitting_on_basis).",
            "Qed.",
            "",
            f"Theorem {name}_coefficients_recovered (a : nat -> D.t) : forall l, (l < {n})%nat ->",
            f"  target_pair 5 (tmap 5 ({name}_functionals l))",
            f"    (SB.tsum 5 {n} (fun j => TB.scale 5 (a j) (tmap 5 ({name}_vectors j)))) = D.mul (H.h {d}) (a l).",
            "Proof.",
            f"  exact (coefficients_recovered 5 {n} {d} {name}_functionals {name}_vectors {name}_functionals_dual a).",
            "Qed.",
            "",
            f"Theorem {name}_combination_zero_coefficients (a : nat -> D.t) :",
            f"  SB.tsum 5 {n} (fun j => TB.scale 5 (a j) (tmap 5 ({name}_vectors j))) = TB.zero 5 ->",
            f"  forall l, (l < {n})%nat -> D.mul (H.h {d}) (a l) = D.zero.",
            "Proof.",
            f"  exact (combination_zero_coefficients 5 {n} {d} {name}_functionals {name}_vectors",
            f"           {name}_functionals_dual a).",
            "Qed.",
            "",
            f"Theorem {name}_kernel_free_basis (inverse : D.t) : D.mul (H.h {d}) inverse = D.one -> forall z,",
            f"  TB.mul 5 (tmap 5 {name}_point) z = TB.zero 5 <->",
            f"  z = SB.tsum 5 {n} (fun j => TB.scale 5 (D.mul inverse "
            + f"(target_pair 5 (tmap 5 ({name}_functionals j)) z))",
            f"                                  (tmap 5 ({name}_vectors j))).",
            "Proof.",
            f"  exact (kernel_free_basis 5 {n} {name}_point {d} {name}_back {name}_functionals {name}_vectors",
            f"           {name}_vectors_annihilated {name}_splitting_on_basis inverse).",
            "Qed.",
            "",
        ]
    out += [
        "End CanonicalKernels.",
        "",
        "(** The statements have a model in which 2 and 50 are invertible: Zmod 7, where 2 4 = 1 and 50 = 1. *)",
        "Module Zmod7 <: CommutativeRing.",
        "  Definition t := Zmod 7.",
        "  Definition zero : t := Zmod.zero.",
        "  Definition one : t := Zmod.one.",
        "  Definition add : t -> t -> t := Zmod.add.",
        "  Definition mul : t -> t -> t := Zmod.mul.",
        "  Definition sub : t -> t -> t := Zmod.sub.",
        "  Definition opp : t -> t := Zmod.opp.",
        "  Lemma ring_th : ring_theory zero one add mul sub opp (@eq t).",
        "  Proof. exact (Zmod.ring_theory 7). Qed.",
        "End Zmod7.",
        "",
        "Module Mod7 := CanonicalKernels Zmod7.",
        "",
    ]
    for record in records:
        name, d = record["name"], record["scalar"]
        inverse = pow(int(d), -1, 7)
        out += [
            f"Definition {name}_kernel_mod7 :=",
            f"  Mod7.{name}_kernel_free_basis (Zmod.of_Z 7 {inverse}) ltac:(vm_compute; reflexivity).",
        ]
    return "\n".join(out) + "\n"


def replace_text(path: Path, text: str) -> None:
    """Write text beside path and rename it over path, so a reader sees the old bytes or the new ones."""
    scratch = path.with_name(path.name + ".new")
    scratch.write_text(text, encoding="utf-8")
    os.replace(scratch, path)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", maxsplit=1)[0])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--generate", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    reps = representatives()
    if args.generate:
        computed = parallel.ordered_map(certificate, list(reps.items()), min_items=1)
        text = json.dumps({"schema": "cd-tower-kernel-certificates-v1", "points": computed}, indent=1)
        # One list of integers per line: a matrix row, a point or a split-coordinate vector.
        text = re.sub(
            r"\[\s+((?:-?\d+,\s+)*-?\d+)\s+\]", lambda found: "[" + " ".join(found.group(1).split()) + "]", text
        )
        text += "\n"
    else:
        text = CERTIFICATES.read_text(encoding="utf-8")
    records = json.loads(text)["points"]
    if [r["name"] for r in records] != list(NULLITY):
        raise ValueError("the certificate data does not list the twelve points in order")
    results = parallel.ordered_map(checked, [(r, reps[r["name"]]) for r in records], min_items=1)
    failed = [r for r in results if r["defects"]]
    for r in results:
        verdict = "ok" if not r["defects"] else r["defects"]
        print(
            f"{r['name']:5s} nullity {r['nullity']:2d} d {r['scalar']:2d} Smith invariants {r['invariants']} {verdict}"
        )
    if failed:
        return 1
    if args.generate:
        # Both texts exist before either file changes, and every regenerated certificate has passed.
        rendering = render(records)
        replace_text(CERTIFICATES, text)
        replace_text(ROCQ_FILE, rendering)
    elif ROCQ_FILE.read_text(encoding="utf-8") != render(records):
        print(f"{ROCQ_FILE.name} is not the rendering of {CERTIFICATES.name}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
