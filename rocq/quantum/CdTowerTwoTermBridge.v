(** Explicit zero products of two-term operands on the commutative-ring
    pair tower: the Rocq bridge of the two headline theorems of the Lean
    module lean/GororobaMath/CayleyDickson/TwoTerm.lean.

    Convention: the tower, product and basis of CdTowerRing.v and
    CdTowerRingBasis.v, (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)),
    with basis k i the basis vector of index i below 2^k, whose top index
    bit selects the second half of the pair; CdTowerBasisBridge.v ties
    basis k i to Lean's e R k p at the bit vector p of value i, makes
    Nat.lxor the index of p ^^^ q, and makes TowerSign.neg_sign Lean's
    Tower.negSign with the same argument order. The Lean negation -x is
    scale k neg_one x, so Lean's e x - e x' is
    add k (basis k x) (scale k neg_one (basis k x')).

    The functor TwoTermBridge transcribes the definitions of the Lean
    module, conjunct for conjunct:

    - partner i j x is Tower.partner i j x = x ^^^ i ^^^ j.
    - aligned_add k i j x is Tower.alignedAdd k i j x, with Lean's
      Boolean a != b written negb (Bool.eqb a b).
    - aligned_sub k i j x is Tower.alignedSub k i j x, with a == b written
      Bool.eqb a b.

    These definitions compose neg_sign with Nat.lxor alone.
    ci/compare_alignment.sh evaluates Lean's Tower.partner,
    Tower.alignedAdd and Tower.alignedSub and the three Rocq definitions on
    every triple of indices below 2^k for k up to 6, and ci/compare_signs.sh
    compares Lean's Tower.sign with neg_sign through TowerSign.sign_sigma.

    It restates the two headline theorems at the coefficient ring D:

    - two_term_mul_add_eq_zero is Tower.two_term_mul_add_eq_zero: an
      aligned pair of opposite signs gives
      (e_i + e_j)(e_x + e_(partner i j x)) = 0, for i, j and x below 2^k.
    - two_term_mul_sub_eq_zero is Tower.two_term_mul_sub_eq_zero: an
      aligned pair of equal signs gives
      (e_i + e_j)(e_x - e_(partner i j x)) = 0, for i, j and x below 2^k.

    The proof expands the product into four basis products with e_mul_e of
    CdTowerBasisBridge.v; lxor_partner_left and lxor_partner_right are
    Tower.xor_partner_left and Tower.xor_partner_right, which pair the four
    terms on two basis vectors, and the alignment hypothesis fixes their
    signs to cancel. pathion_e1_add_e18_mul_e5_add_e22,
    pathion_e1_add_e18_mul_e4_sub_e23 and
    sedenion_e1_add_e10_mul_e5_add_e14 are the three zero divisors of the
    Lean module, stated at every coefficient ring D as Lean states them at
    every ring.

    The Rocq statements are narrower than the Lean ones: the coefficients
    form a commutative ring whose conjugation is the identity (the
    signature CommutativeRing), where Lean takes every NonAssocRing with a
    StarRing, and an index is a nat below 2^k, where Lean takes a
    BitVec k. IntegerTwoTermBridge instantiates the functor at the
    integers; integer_aligned_e1_e18 evaluates the alignment tests that the
    Lean module decides for its zero divisors, and integer_aligned_count_e1_e18
    counts 24 aligned indices of the operand e_1 + e_18 at level 5, the 12
    pairs of Lean's Tower.alignedPairCount_pathion_1_18. *)

From Stdlib Require Import Ring Lia PeanoNat ZArith List.
Require Import CdTowerRing CdTowerRingBasis CdTowerRingBaseChange.
Require CdTowerBasisSign.
Require Import CdTowerBasisBridge.

Module TwoTermBridge (D : CommutativeRing).
Module BB := TowerBasisBridge D.
Import BB BB.B BB.B.T TowerSign.
Add Ring two_term_bridge_ring : D.ring_th.

Definition partner (i j x : nat) : nat := Nat.lxor (Nat.lxor x i) j.

Definition aligned_add (k i j x : nat) : bool :=
  andb (negb (Bool.eqb (neg_sign k i x) (neg_sign k j (partner i j x))))
    (negb (Bool.eqb (neg_sign k j x) (neg_sign k i (partner i j x)))).

Definition aligned_sub (k i j x : nat) : bool :=
  andb (Bool.eqb (neg_sign k i x) (neg_sign k j (partner i j x)))
    (Bool.eqb (neg_sign k j x) (neg_sign k i (partner i j x))).

Lemma lxor_partner_left i j x : Nat.lxor i (partner i j x) = Nat.lxor j x.
Proof.
  unfold partner. apply Nat.bits_inj. intro n. rewrite !Nat.lxor_spec.
  destruct (Nat.testbit i n), (Nat.testbit j n), (Nat.testbit x n); reflexivity.
Qed.

Lemma lxor_partner_right i j x : Nat.lxor j (partner i j x) = Nat.lxor i x.
Proof.
  unfold partner. apply Nat.bits_inj. intro n. rewrite !Nat.lxor_spec.
  destruct (Nat.testbit i n), (Nat.testbit j n), (Nat.testbit x n); reflexivity.
Qed.

Lemma partner_lt k i j x : (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat -> (x < Nat.pow 2 k)%nat ->
  (partner i j x < Nat.pow 2 k)%nat.
Proof. intros Hi Hj Hx. unfold partner. apply CdTowerBasisSign.lxor_lt; [apply CdTowerBasisSign.lxor_lt |]; assumption. Qed.

(** Tower.two_term_mul_add_eq_zero: an aligned pair of opposite signs
    gives (e_i + e_j)(e_x + e_x') = 0 with x' = partner i j x. *)
Theorem two_term_mul_add_eq_zero k i j x :
  (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat -> (x < Nat.pow 2 k)%nat ->
  aligned_add k i j x = true ->
  mul k (add k (basis k i) (basis k j)) (add k (basis k x) (basis k (partner i j x))) = zero k.
Proof.
  intros Hi Hj Hx H. pose proof (partner_lt k i j x Hi Hj Hx) as Hp.
  rewrite mul_add_l, !mul_add_r, !e_mul_e by assumption.
  rewrite lxor_partner_left, lxor_partner_right.
  revert H. unfold aligned_add.
  destruct (neg_sign k i x), (neg_sign k j (partner i j x)), (neg_sign k j x),
    (neg_sign k i (partner i j x)); intro H; cbn [andb negb Bool.eqb] in H; try discriminate H; vec.
Qed.

(** Tower.two_term_mul_sub_eq_zero: an aligned pair of equal signs gives
    (e_i + e_j)(e_x - e_x') = 0 with x' = partner i j x. *)
Theorem two_term_mul_sub_eq_zero k i j x :
  (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat -> (x < Nat.pow 2 k)%nat ->
  aligned_sub k i j x = true ->
  mul k (add k (basis k i) (basis k j))
    (add k (basis k x) (scale k neg_one (basis k (partner i j x)))) = zero k.
Proof.
  intros Hi Hj Hx H. pose proof (partner_lt k i j x Hi Hj Hx) as Hp.
  rewrite mul_add_l, !mul_add_r, !mul_scale_r, !e_mul_e by assumption.
  rewrite lxor_partner_left, lxor_partner_right.
  revert H. unfold aligned_sub.
  destruct (neg_sign k i x), (neg_sign k j (partner i j x)), (neg_sign k j x),
    (neg_sign k i (partner i j x)); intro H; cbn [andb negb Bool.eqb] in H; try discriminate H; vec.
Qed.

Lemma lt_pow (n k : nat) : Nat.ltb n (Nat.pow 2 k) = true -> (n < Nat.pow 2 k)%nat.
Proof. apply Nat.ltb_lt. Qed.

(** Tower.pathion_e1_add_e18_mul_e5_add_e22: (e_1 + e_18)(e_5 + e_22) = 0
    at level 5. *)
Theorem pathion_e1_add_e18_mul_e5_add_e22 :
  mul 5 (add 5 (basis 5 1) (basis 5 18)) (add 5 (basis 5 5) (basis 5 22)) = zero 5.
Proof.
  exact (two_term_mul_add_eq_zero 5 1 18 5 (lt_pow 1 5 eq_refl) (lt_pow 18 5 eq_refl)
    (lt_pow 5 5 eq_refl) eq_refl).
Qed.

(** Tower.pathion_e1_add_e18_mul_e4_sub_e23: (e_1 + e_18)(e_4 - e_23) = 0
    at level 5. *)
Theorem pathion_e1_add_e18_mul_e4_sub_e23 :
  mul 5 (add 5 (basis 5 1) (basis 5 18)) (add 5 (basis 5 4) (scale 5 neg_one (basis 5 23))) = zero 5.
Proof.
  exact (two_term_mul_sub_eq_zero 5 1 18 4 (lt_pow 1 5 eq_refl) (lt_pow 18 5 eq_refl)
    (lt_pow 4 5 eq_refl) eq_refl).
Qed.

(** Tower.sedenion_e1_add_e10_mul_e5_add_e14: (e_1 + e_10)(e_5 + e_14) = 0
    at level 4. *)
Theorem sedenion_e1_add_e10_mul_e5_add_e14 :
  mul 4 (add 4 (basis 4 1) (basis 4 10)) (add 4 (basis 4 5) (basis 4 14)) = zero 4.
Proof.
  exact (two_term_mul_add_eq_zero 4 1 10 5 (lt_pow 1 4 eq_refl) (lt_pow 10 4 eq_refl)
    (lt_pow 5 4 eq_refl) eq_refl).
Qed.

End TwoTermBridge.

Module IntegerTwoTermBridge := TwoTermBridge IntegerRing.

(** The alignment tests that the Lean module decides for its zero
    divisors: x = 5 is aligned with opposite signs and x = 4 with equal
    signs under e_1 + e_18 at level 5, with partners 22 and 23, and x = 5
    under e_1 + e_10 at level 4, with partner 14. *)
Example integer_aligned_e1_e18 :
  IntegerTwoTermBridge.aligned_add 5 1 18 5 = true /\ IntegerTwoTermBridge.partner 1 18 5 = 22%nat /\
  IntegerTwoTermBridge.aligned_sub 5 1 18 4 = true /\ IntegerTwoTermBridge.partner 1 18 4 = 23%nat /\
  IntegerTwoTermBridge.aligned_add 5 1 18 4 = false /\
  IntegerTwoTermBridge.aligned_add 4 1 10 5 = true /\ IntegerTwoTermBridge.partner 1 10 5 = 14%nat.
Proof. vm_compute. repeat split. Qed.

(** 24 indices below 32 are aligned under e_1 + e_18, the 12 pairs of
    Lean's Tower.alignedPairCount_pathion_1_18; under e_1 + e_17 none is,
    as Tower.alignedPairCount_pathion_1_17 states. *)
Example integer_aligned_count_e1_e18 :
  length (filter (fun x => orb (IntegerTwoTermBridge.aligned_add 5 1 18 x)
    (IntegerTwoTermBridge.aligned_sub 5 1 18 x)) (seq 0 32)) = 24%nat /\
  length (filter (fun x => orb (IntegerTwoTermBridge.aligned_add 5 1 17 x)
    (IntegerTwoTermBridge.aligned_sub 5 1 17 x)) (seq 0 32)) = 0%nat.
Proof. vm_compute. split; reflexivity. Qed.
