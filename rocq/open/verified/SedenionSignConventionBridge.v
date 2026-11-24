(** * The sedenion sign table [sed_sign] is the basis product of [tz_mul].

    Convention.  [C1467_XORSignCocycle] fixes the sedenion product of basis
    units by the 16x16 table [sed_sign]: e_i e_j = sed_sign i j e_(i xor j).
    [C1468_SlotEmbeddingAllPairs] fixes the integer Cayley-Dickson tower
    [tz] with the product [tz_mul]: (a, b)(c, d) = (a c - conj(d) b,
    d a + b conj(c)), and the unit e_i is [tz_basis 4 i].  The box-kite
    census files ([BoxKiteSignCensus], [BoxKiteTwoBladeCensus],
    [C1467_OctonionFanoTriples], [C1630_BasisAssociatorTensor],
    [C468_EmanationTable]) count with the first; the annihilator and
    participation-graph files ([C014_AnnihilatorCensus],
    [C946_ZDParticipationGraph]) count with the second.

    Result.  [sed_sign_is_tz_mul_basis_product]: for every pair of indices
    below 16, [tz_mul 4 (tz_basis 4 i) (tz_basis 4 j)] equals
    [tz_basis 4 (i xor j)] when [sed_sign i j = 1] and its negation when
    [sed_sign i j = -1], and [sed_sign] takes no other value there.  The two
    conventions are therefore one algebra on the basis, decided by
    evaluation ([vm_compute]) over the 256 pairs. *)

From Stdlib Require Import Arith PeanoNat Bool List ZArith.
From OpenGororobaVerified Require Import C1467_XORSignCocycle C1468_SlotEmbeddingAllPairs.
Import ListNotations.

(** The signed unit [s e_k] for a sign [s] in {1, -1}. *)
Definition signed_basis (s : Z) (k : nat) : tz 4 :=
  if Z.eqb s 1%Z then tz_basis 4 k else tz_neg 4 (tz_basis 4 k).

Definition basis_product_agrees (i j : nat) : bool :=
  (Z.eqb (sed_sign i j) 1%Z || Z.eqb (sed_sign i j) (-1)%Z)%bool
  && tz_eqb 4 (tz_mul 4 (tz_basis 4 i) (tz_basis 4 j))
                (signed_basis (sed_sign i j) (Nat.lxor i j)).

Lemma basis_product_table :
  forallb (fun i => forallb (basis_product_agrees i) (seq 0 16)) (seq 0 16) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem sed_sign_is_tz_mul_basis_product :
  forall i j, i < 16 -> j < 16 ->
    (sed_sign i j = 1%Z \/ sed_sign i j = (-1)%Z) /\
    tz_mul 4 (tz_basis 4 i) (tz_basis 4 j)
    = signed_basis (sed_sign i j) (Nat.lxor i j).
Proof.
  intros i j Hi Hj.
  pose proof basis_product_table as H.
  rewrite forallb_forall in H.
  specialize (H i (proj2 (in_seq 16 0 i) (conj (Nat.le_0_l i) Hi))).
  rewrite forallb_forall in H.
  specialize (H j (proj2 (in_seq 16 0 j) (conj (Nat.le_0_l j) Hj))).
  unfold basis_product_agrees in H.
  apply andb_prop in H as [Hs He].
  split.
  - apply orb_prop in Hs as [Hs | Hs]; apply Z.eqb_eq in Hs; [left | right]; exact Hs.
  - exact (tz_eqb_true 4 _ _ He).
Qed.

(** Negative control: e_1 e_2 is e_3 (sed_sign 1 2 = 1), so the opposite
    sign is refuted by evaluation. *)
Lemma basis_product_wrong_sign_refuted :
  tz_mul 4 (tz_basis 4 1) (tz_basis 4 2) <> signed_basis (-1)%Z 3.
Proof. vm_compute. discriminate. Qed.

Print Assumptions sed_sign_is_tz_mul_basis_product.
