"""Render a Hilbert-cell source of rocq/quantum from a cell certificate export.

The input is the a5-hilbert-cell-certificate-v1 file of ledger row A5-108 (E8-bar to VB, p = 32029,
d = 1; output HilbertCellA5_108.v) or of row A5-111 (p = 32029, d = 4; output HilbertCellA5_111.v). Only a
file with the pinned sha256 of one of the two rows is accepted. The output holds the J and G tables of the
canonical header, the sparse operators, levels, vector e and left inverse as a `cert` of
HilbertCellCertificate.v, the proof that check_cert accepts it, and the cell statement (A5-108) or its
independence half (A5-111).

Usage: hilbert_cell_certificate.py INPUT.json --write
       hilbert_cell_certificate.py INPUT.json --check
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

CELLS = {
    "A5-108": {
        "sha256": "bd2755fe13df2465ac97852b0ad15fc99e8bc754f96b122adb450dac0ed97af5",
        "prime": 32029,
        "d": 1,
        "h": 10,
        "name": "a5_108",
        "output": "HilbertCellA5_108.v",
        "spans": True,
    },
    "A5-111": {
        "sha256": "ccbf15218b63059d8bd55bf9dabfdbbdbaabd4d960df01ce6c3ef6c228d21705",
        "prime": 32029,
        "d": 4,
        "h": 155,
        "name": "a5_111",
        "output": "HilbertCellA5_111.v",
        "spans": False,
    },
}
SCHEMA = "a5-hilbert-cell-certificate-v1"
GENERATOR = "ci/quantum-sources/hilbert_cell_certificate.py"
ROOT = Path(__file__).resolve().parents[2]
QUANTUM = ROOT / "rocq" / "quantum"
TERMS_PER_LINE = 2


def fail(message: str) -> None:
    sys.exit(f"hilbert_cell_certificate: {message}")


def load(path: Path) -> tuple[str, dict]:
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    for ledger_id, cell in CELLS.items():
        if cell["sha256"] == digest:
            cert = json.loads(data)
            if cert.get("ledger_id") != ledger_id:
                fail(f"the pinned file of {ledger_id} names another ledger id")
            return ledger_id, cert
    fail(f"input sha256 {digest} is not the pinned digest of any cell")
    raise AssertionError("unreachable")


def msets_order(count: int, degree: int) -> list[tuple[int, ...]]:
    """Index tuples in the order of msets of HilbertCellCertificate.v."""

    def rec(start: int, d: int) -> list[tuple[int, ...]]:
        if d == 0:
            return [()]
        out: list[tuple[int, ...]] = []
        for k in range(start, count):
            out.extend((k, *rest) for rest in rec(k, d - 1))
        return out

    return rec(0, degree)


def selected_positions(cert: dict) -> list[int]:
    """Positions of the selected products in the msets order of the checker."""
    products = cert["products"]
    order = msets_order(len(cert["header"]["G"]), cert["d"])
    tuples = [tuple(t) for t in products["tuples"]]
    if sorted(order) != sorted(tuples) or len(set(tuples)) != len(tuples):
        fail("the product tuples are not the multisets of the generators")
    position = {t: i for i, t in enumerate(order)}
    return [position[tuples[j]] for j in products["selected"]]


def validate(ledger_id: str, cert: dict) -> None:
    cell = CELLS[ledger_id]
    if cert.get("schema") != SCHEMA or cert.get("ledger_id") != ledger_id:
        fail("unexpected schema or ledger id")
    if cert["prime"] != cell["prime"] or cert["d"] != cell["d"] or cert["h_claimed"] != cell["h"]:
        fail("unexpected prime, degree or claimed value")
    if not cert["J_in_W"] or cert["products"]["mode"] != "all":
        fail("the export does not certify J in W or all products")
    n = len(cert["header"]["vars"])
    module = cert["module"]
    q = module["q"]
    for table in ("J", "G"):
        for poly in cert["header"][table]:
            for coefficient, exponents in poly:
                if len(exponents) != n or not 0 <= coefficient < cert["prime"]:
                    fail("malformed term in the header tables")
    if len(module["basis"]) != q or len(module["lev"]) != q or len(module["M"]) != n:
        fail("operator or level tables have the wrong shape")
    for matrix in module["M"]:
        for row, col, value in matrix:
            if not (0 <= row < q and 0 <= col < q and 0 <= value < cert["prime"]):
                fail("operator entry out of range")
    left = cert["products"]["left_inverse"]
    if len(left) != cert["products"]["r"] or any(len(r) != q for r in left):
        fail("left inverse has the wrong shape")
    if module["e"] != 0 or module["basis"][0] != [0] * n:
        fail("e is not the class of 1")


def mono(exponents: list[int]) -> str:
    return "m8 " + " ".join(str(x) for x in exponents)


def poly_block(name_poly: list) -> str:
    terms = [f"({mono(exponents)}, {coefficient})" for coefficient, exponents in name_poly]
    lines = []
    for i in range(0, len(terms), TERMS_PER_LINE):
        lines.append("    " + "; ".join(terms[i : i + TERMS_PER_LINE]))
    return "  [\n" + ";\n".join(lines) + " ]"


def poly_list(name: str, polys: list) -> str:
    body = ";\n".join(poly_block(p) for p in polys)
    return f"Definition {name} : list poly :=\n[\n{body} ].\n"


def sparse_row(entries: list[tuple[int, int]]) -> str:
    """One row; the key of column c is c + 1, the positive number HilbertCellCertificate.v reads."""
    return "[" + "; ".join(f"sp {c + 1} {v}" for c, v in entries) + "]"


def operator(entries: list, q: int) -> str:
    rows: list[list[tuple[int, int]]] = [[] for _ in range(q)]
    for row, col, value in sorted(entries):
        rows[row].append((col, value))
    return "  [ " + ";\n    ".join(sparse_row(r) for r in rows) + " ]"


def render(ledger_id: str, cert: dict) -> str:
    validate(ledger_id, cert)
    cell = CELLS[ledger_id]
    name = cell["name"]
    module = cert["module"]
    q = module["q"]
    r = cert["products"]["r"]
    n = len(cert["header"]["vars"])
    positions = selected_positions(cert)
    ops = ";\n".join(operator(m, q) for m in module["M"])
    left_rows = [sparse_row([(c, v) for c, v in enumerate(row) if v != 0]) for row in cert["products"]["left_inverse"]]
    e_vector = [1 if i == module["e"] else 0 for i in range(q)]
    pieces = [
        HEADER.format(
            generator=GENERATOR,
            digest=cell["sha256"],
            prime=cert["prime"],
            n=n,
            r=r,
            name=name.upper().replace("_", "-"),
            d=cert["d"],
        ),
        poly_list(f"{name}_J", cert["header"]["J"]),
        poly_list(f"{name}_G", cert["header"]["G"]),
        f"Definition {name}_ops : list spmat :=\n[\n" + ops + " ].\n",
        f"Definition {name}_lev : list nat := [" + "; ".join(f"{x}%nat" for x in module["lev"]) + "].\n",
        f"Definition {name}_e : vec := [" + "; ".join(str(x) for x in e_vector) + "].\n",
        f"Definition {name}_left : spmat :=\n  [ " + ";\n    ".join(left_rows) + " ].\n",
        f"Definition {name}_sel : list nat := [" + "; ".join(f"{x}%nat" for x in positions) + "].\n",
        fill(TAIL_COMMON, name=name, prime=cert["prime"], n=n, d=cert["d"]),
        fill(
            TAIL_SPANS if cell["spans"] else TAIL_INDEPENDENT,
            name=name,
            prime=cert["prime"],
            n=n,
            d=cert["d"],
            h=cert["h_claimed"],
        ),
    ]
    return "\n".join(pieces)


HEADER = r"""(** * The cell {name}: h_{d} = {r} for E8-bar to VB over F_{prime}.

    Generated by {generator} from the cell certificate export with sha256 {digest}.
    Run the generator with --check to bind this source to that file.

    Convention: HilbertCellCertificate.v fixes the statement ([hilbert_cell]) and the checker ([check_cert]).
    The tables below are the J and G polynomials of the canonical header in {n} variables, each term a
    (monomial, coefficient) pair with the exponent vector written by [m8]; the operators are the {n}
    sparse matrices of multiplication by the variables on the quotient basis, row b listing the pairs
    (key, value) by [sp], the key of column c being c + 1. The selected products are positions in the order of
    [products]; the checker enumerates the products as vectors, so no product polynomial is expanded. *)

From Stdlib Require Import ZArith Lia List Znumtheory.
Require Import HilbertCellCertificate.
Import ListNotations.
Open Scope Z_scope.

Definition m8 (a b c d e f g h : nat) : mono := [a; b; c; d; e; f; g; h].

Definition sp (c : positive) (v : Z) : positive * Z := (c, v).

Arguments sp c%_positive v%_Z.
"""

TAIL_COMMON = r"""
Definition @NAME@_cert : cert :=
  mk_cert @NAME@_ops @NAME@_lev @NAME@_e @NAME@_left @NAME@_sel.

Lemma @NAME@_cert_accepted : check_cert @PRIME@ @N@ @NAME@_J @NAME@_G @D@ @NAME@_cert = true.
Proof. vm_compute. reflexivity. Qed.

Lemma in_trial (B : nat) (d : Z) :
  2 <= d -> d <= Z.of_nat B -> In d (map Z.of_nat (seq 2 (B - 1))).
Proof.
  intros H1 H2. apply in_map_iff. exists (Z.to_nat d). split.
  - apply Z2Nat.id. lia.
  - apply in_seq. lia.
Qed.

Lemma prime_by_trial (n : Z) (B : nat) :
  1 < n -> n <= Z.of_nat B * Z.of_nat B ->
  forallb (fun d => negb (Z.eqb (n mod d) 0)) (map Z.of_nat (seq 2 (B - 1))) = true ->
  Z.prime n.
Proof.
  intros H1 H2 Hf. split; [exact H1|].
  intros m Hm Hdiv. rewrite forallb_forall in Hf.
  assert (Hbad : forall d, 2 <= d -> d <= Z.of_nat B -> Z.divide d n -> False).
  { intros d Hd1 Hd2 Hd. pose proof (Hf d (in_trial B d Hd1 Hd2)) as H0.
    apply Bool.negb_true_iff in H0. apply Z.eqb_neq in H0. apply H0.
    apply Z.mod_divide; [lia | exact Hd]. }
  destruct Hdiv as [k Hk].
  destruct (Z_le_gt_dec m (Z.of_nat B)) as [Hle|Hgt].
  - apply (Hbad m); [lia | exact Hle | exists k; exact Hk].
  - assert (Hk2 : 2 <= k) by nia.
    assert (Hkb : k <= Z.of_nat B) by nia.
    apply (Hbad k Hk2 Hkb). exists m. lia.
Qed.

Lemma prime_@PRIME@ : prime @PRIME@.
Proof.
  apply prime_alt.
  apply (prime_by_trial @PRIME@ 179);
    [lia | first [lia | (vm_compute; intros H; discriminate H)] | vm_compute; reflexivity].
Qed.

"""

TAIL_SPANS = r"""Definition unit_cs (r i : nat) : list Z :=
  map (fun j => if Nat.eqb j i then 1 else 0) (seq 0 r).

Lemma length_unit_cs r i : length (unit_cs r i) = r.
Proof. unfold unit_cs. rewrite length_map, length_seq. reflexivity. Qed.

Lemma kcoef_notin (f : poly) m : ~ In m (map fst f) -> pcoef f m = 0.
Proof.
  unfold pcoef. induction f as [|t f IH]; intros H; [reflexivity|].
  simpl in H. simpl. destruct (mono_eq_dec (fst t) m) as [E|NE].
  - exfalso. apply H. left. exact E.
  - rewrite IH by (intro HI; apply H; right; exact HI). reflexivity.
Qed.

Definition pzero_b (p : Z) (f : poly) : bool :=
  forallb (fun m => Z.eqb (pcoef f m mod p) 0) (map fst f).

Lemma pzero_b_sound p f : pzero_b p f = true -> pzero p f.
Proof.
  intros H m. destruct (in_dec mono_eq_dec m (map fst f)) as [Hi|Hn].
  - unfold pzero_b in H. rewrite forallb_forall in H.
    apply cg_zero_of_mod. apply Z.eqb_eq. exact (H m Hi).
  - rewrite (kcoef_notin f m Hn). apply cg_refl.
Qed.

Lemma spans_of_check p n gens prods reps u cofs :
  wf_poly n u -> Forall (wf_poly n) cofs -> length cofs = length gens ->
  ~ cg p (const_coef u) 0 ->
  forallb (fun i => pzero_b p (padd (pmul u (padd (nth i prods [])
                         (pneg (lincomb (unit_cs (length reps) i) reps))))
                       (pneg (combo cofs gens)))) (seq 0 (length prods)) = true ->
  spans_mod p n gens prods reps.
Proof.
  intros Hu Hc Hl Hnz Hf rho Hin.
  destruct (In_nth prods rho [] Hin) as [i [Hi Hni]].
  exists (unit_cs (length reps) i). split; [apply length_unit_cs|].
  exists u, cofs. refine (conj Hu (conj Hc (conj Hl (conj Hnz _)))).
  rewrite forallb_forall in Hf.
  specialize (Hf i (proj2 (in_seq _ _ _) (conj (Nat.le_0_l i) Hi))).
  rewrite Hni in Hf. apply pzero_b_sound. exact Hf.
Qed.

Lemma wf_repeat_nil n k : Forall (wf_poly n) (repeat ([] : poly) k).
Proof. induction k as [|k IH]; simpl; constructor; [constructor | exact IH]. Qed.

Lemma not_cg_one : ~ cg 32029 1 0.
Proof. unfold cg. intros [k Hk]. destruct (Z_le_gt_dec k 0); lia. Qed.

Theorem @NAME@_hilbert_cell : hilbert_cell 32029 8 @NAME@_J @NAME@_G 1 10.
Proof.
  exists (c_sel @NAME@_cert).
  refine (conj _ (conj _ (conj _ _))).
  - vm_compute. reflexivity.
  - exact (check_cert_sel_range _ _ _ _ _ _ @NAME@_cert_accepted).
  - exact (cert_independent 32029 8 _ _ 1 @NAME@_cert prime_32029 @NAME@_cert_accepted).
  - apply (spans_of_check 32029 8 _ _ _ (one_poly 8)
             (repeat ([] : poly) (length (@NAME@_J ++ m_products 8 @NAME@_G 1)))).
    + unfold wf_poly, one_poly. constructor; [reflexivity | constructor].
    + apply wf_repeat_nil.
    + apply repeat_length.
    + exact not_cg_one.
    + vm_compute. reflexivity.
Qed.
"""

TAIL_INDEPENDENT = r"""
Theorem @NAME@_independent :
  exists sel : list nat, length sel = @H@%nat /\
    (forall i, In i sel -> (i < length (products @N@ @NAME@_G @D@))%nat) /\
    independent_mod @PRIME@ @N@ (@NAME@_J ++ m_products @N@ @NAME@_G @D@)
      (select_products @N@ @NAME@_G @D@ sel).
Proof.
  exists (c_sel @NAME@_cert).
  refine (conj _ (conj _ _)).
  - vm_compute. reflexivity.
  - exact (check_cert_sel_range _ _ _ _ _ _ @NAME@_cert_accepted).
  - exact (cert_independent @PRIME@ @N@ _ _ @D@ @NAME@_cert prime_@PRIME@ @NAME@_cert_accepted).
Qed.
"""


def fill(text: str, **values: object) -> str:
    """Replace each @KEY@ placeholder of a template by its value."""
    for key, value in values.items():
        text = text.replace(f"@{key.upper()}@", str(value))
    return text


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="the pinned cell certificate JSON")
    actions = parser.add_mutually_exclusive_group(required=True)
    actions.add_argument("--write", action="store_true", help="write the Rocq source")
    actions.add_argument("--check", action="store_true", help="require the tracked source to equal the rendering")
    args = parser.parse_args()
    ledger_id, cert = load(args.input)
    text = render(ledger_id, cert)
    output = QUANTUM / CELLS[ledger_id]["output"]
    if args.write:
        output.write_text(text, encoding="utf-8")
        print(f"wrote {output.relative_to(ROOT)}")
        return
    if not output.is_file() or output.read_text(encoding="utf-8") != text:
        fail(f"{output.relative_to(ROOT)} differs from the rendering")
    print("ok")


if __name__ == "__main__":
    main()
