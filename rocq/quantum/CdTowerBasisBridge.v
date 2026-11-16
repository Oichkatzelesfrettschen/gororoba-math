(** The basis products and signs of the commutative-ring pair tower: the
    Rocq bridge of the six headline theorems of the Lean module
    lean/GororobaMath/CayleyDickson/Tower.lean.

    Convention: the tower, product and basis of CdTowerRing.v and
    CdTowerRingBasis.v, (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)),
    with basis k i the basis vector of index i below 2^k, whose top index
    bit selects the second half of the pair. The Lean tower has the same
    product, and its basis element e R k p, for p : BitVec k, lies in the
    second half exactly when the most significant bit of p is set, so
    basis k i is e R k p at the bit vector p of value i; the low part
    p.setWidth k of a bit vector of width k + 1 is i - 2^k when the top
    bit is set and i otherwise, and BitVec.toNat_xor makes p ^^^ q the
    index Nat.lxor i j. The Lean negation -x is scale k neg_one x, and the
    Lean unit 1 is one k.

    TowerSign.neg_sign k p q is Lean's Tower.negSign on nat indices, with
    its four top-bit branches in the same order, and TowerSign.sign is
    Tower.sign, -1 when neg_sign holds and 1 otherwise. TowerSign.sign_sigma
    proves sign k p q = CdTowerBasisSign.sigma k p q for every k, p and q.
    SignBridge.v names that same sigma, and ci/compare_signs.sh compares
    Lean Tower.sign with it on every index pair of the levels it runs, so
    the comparison covers neg_sign through sign_sigma.

    - TowerSign.neg_sign_xor_right is Tower.negSign_xor_right, for p and q
      below 2^k. Its proof reads sigma_left_involution and sigma_zero_l of
      CdTowerBasisSign.v through sign_sigma.

    The functor TowerBasisBridge restates the other five theorems at the
    coefficient ring D:

    - star_e is Tower.star_e, for p below 2^k.
    - e_mul_e is Tower.e_mul_e, for p and q below 2^k.
    - e_mul_e_sign is Tower.e_mul_e_sign: the integer sign acts on the
      tower through H.h, the ring map from the integers to D of
      CdTowerRingBaseChange.v (IntegerHom), as the integer action of Lean's
      zsmul does.
    - e_mul_self is Tower.e_mul_self, for p below 2^k and p <> 0.
    - e_mul_e_anticomm is Tower.e_mul_e_anticomm, for p and q below 2^k.

    The basis products of CdTowerBasisSign.v (basis_mul, conj_basis) are
    stated over the integer tower of CdImaginarySumConference.v, a type of
    its own, so star_e and e_mul_e repeat their inductions on the functor
    tower with neg_sign in place of sigma, reusing the index lemmas
    lxor_lt, lxor_high_l, lxor_high_r, lxor_high_lr and split_high.
    e_mul_self and e_mul_e_anticomm follow from e_mul_e with
    sigma_diagonal and sigma_anticommute of CdTowerBasisSign.v, read
    through sign_sigma.

    The Rocq statements are narrower than the Lean ones: the coefficients
    form a commutative ring whose conjugation is the identity (the
    signature CommutativeRing), where Lean takes every NonAssocRing with a
    StarRing, and an index is a nat below 2^k, where Lean takes a
    BitVec k. IntegerTowerBasisBridge instantiates the functor at the
    integers (IntegerRing), and integer_e3_e5 evaluates one product of
    level 3 there. *)

From Stdlib Require Import Ring Lia PeanoNat ZArith.
Require Import CdTowerRing CdTowerRingBasis CdTowerRingBaseChange.
Require CdTowerBasisSign.

Module TowerSign.

Fixpoint neg_sign (k : nat) (p q : nat) : bool :=
  match k with
  | O => false
  | S j =>
      let h := Nat.pow 2 j in
      if Nat.ltb p h then
        if Nat.ltb q h then neg_sign j p q else neg_sign j (q - h) p
      else if Nat.ltb q h then xorb (negb (Nat.eqb q 0)) (neg_sign j (p - h) q)
      else if Nat.eqb (q - h) 0 then true else neg_sign j (q - h) (p - h)
  end.

Definition sign (k p q : nat) : Z := if neg_sign k p q then (-1)%Z else 1%Z.

Lemma neg_sign_unfold j p q : neg_sign (S j) p q =
  if Nat.ltb p (Nat.pow 2 j) then
    if Nat.ltb q (Nat.pow 2 j) then neg_sign j p q else neg_sign j (q - Nat.pow 2 j) p
  else if Nat.ltb q (Nat.pow 2 j) then xorb (negb (Nat.eqb q 0)) (neg_sign j (p - Nat.pow 2 j) q)
  else if Nat.eqb (q - Nat.pow 2 j) 0 then true else neg_sign j (q - Nat.pow 2 j) (p - Nat.pow 2 j).
Proof. reflexivity. Qed.

Theorem sign_sigma k : forall p q, sign k p q = CdTowerBasisSign.sigma k p q.
Proof.
  induction k as [|j IH]; intros p q; [reflexivity |].
  rewrite CdTowerBasisSign.sigma_unfold. unfold CdTowerBasisSign.unit_conj.
  rewrite <- !IH. unfold sign. rewrite neg_sign_unfold.
  destruct (Nat.ltb p (Nat.pow 2 j)), (Nat.ltb q (Nat.pow 2 j));
    try destruct (Nat.eqb q 0); try destruct (Nat.eqb (q - Nat.pow 2 j) 0);
    repeat match goal with |- context [neg_sign ?a ?b ?c] => destruct (neg_sign a b c) end;
    reflexivity.
Qed.

Lemma sign_cases k p q :
  (neg_sign k p q = true /\ CdTowerBasisSign.sigma k p q = (-1)%Z) \/
  (neg_sign k p q = false /\ CdTowerBasisSign.sigma k p q = 1%Z).
Proof. rewrite <- sign_sigma. unfold sign. destruct (neg_sign k p q); [left | right]; split; reflexivity. Qed.

Lemma neg_sign_zero_l k q : neg_sign k 0 q = false.
Proof.
  pose proof (CdTowerBasisSign.sigma_zero_l k q) as Z1.
  destruct (sign_cases k 0 q) as [[E S] | [E _]]; [rewrite S in Z1; discriminate | exact E].
Qed.

Lemma neg_sign_self k p : (p < Nat.pow 2 k)%nat -> p <> O -> neg_sign k p p = true.
Proof.
  intros Hp Hp0. pose proof (CdTowerBasisSign.sigma_diagonal k p Hp Hp0) as D1.
  destruct (sign_cases k p p) as [[E _] | [_ S]]; [exact E | rewrite S in D1; discriminate].
Qed.

Lemma neg_sign_swap k p q : (p < Nat.pow 2 k)%nat -> (q < Nat.pow 2 k)%nat ->
  p <> O -> q <> O -> p <> q -> neg_sign k q p = negb (neg_sign k p q).
Proof.
  intros Hp Hq Hp0 Hq0 Hpq.
  pose proof (CdTowerBasisSign.sigma_anticommute k p q Hp Hq Hp0 Hq0 Hpq) as A.
  destruct (sign_cases k p q) as [[E1 S1] | [E1 S1]], (sign_cases k q p) as [[E2 S2] | [E2 S2]];
    rewrite E1, E2; rewrite S1, S2 in A; cbn in A |- *; congruence.
Qed.

(** Tower.negSign_xor_right: the sign of e_p e_(p XOR q) is that of
    e_p e_q, reversed for p <> 0. *)
Theorem neg_sign_xor_right k p q : (p < Nat.pow 2 k)%nat -> (q < Nat.pow 2 k)%nat ->
  neg_sign k p (Nat.lxor p q) = xorb (negb (Nat.eqb p 0)) (neg_sign k p q).
Proof.
  intros Hp Hq. destruct (Nat.eq_dec p 0) as [-> | Hp0].
  - rewrite Nat.lxor_0_l, !neg_sign_zero_l. reflexivity.
  - rewrite (proj2 (Nat.eqb_neq p 0) Hp0).
    pose proof (CdTowerBasisSign.sigma_left_involution k p q Hp Hq Hp0) as L.
    destruct (sign_cases k p q) as [[E1 S1] | [E1 S1]],
      (sign_cases k p (Nat.lxor p q)) as [[E2 S2] | [E2 S2]];
      rewrite E1, E2; rewrite S1, S2 in L; cbn in L |- *; congruence.
Qed.

End TowerSign.

Module TowerBasisBridge (D : CommutativeRing).
Module B := RingTowerBasis D.
Module H := IntegerHom D.
Import B B.T TowerSign.
Add Ring tower_basis_bridge_ring : D.ring_th.

Lemma scale_one k x : scale k D.one x = x.
Proof. vec. Qed.

Lemma basis_low j c : (c < Nat.pow 2 j)%nat -> basis (S j) c = (basis j c, zero j).
Proof. intro Hc. cbn [basis]. rewrite (proj2 (Nat.ltb_lt _ _) Hc). reflexivity. Qed.

Lemma basis_high j c : (c < Nat.pow 2 j)%nat -> basis (S j) (c + Nat.pow 2 j) = (zero j, basis j c).
Proof.
  intro Hc. cbn [basis]. rewrite (proj2 (Nat.ltb_ge _ _)) by lia. rewrite Nat.add_sub. reflexivity.
Qed.

Lemma basis_zero k : basis k 0 = one k.
Proof.
  induction k as [|j IH]; [reflexivity |].
  rewrite basis_low by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia). rewrite IH. reflexivity.
Qed.

Lemma high_nonzero j c : Nat.eqb (c + Nat.pow 2 j) 0 = false.
Proof. apply Nat.eqb_neq. pose proof (Nat.pow_nonzero 2 j ltac:(lia)). lia. Qed.

(** Tower.star_e: conjugation fixes e_0 = 1 and negates every other
    basis vector. *)
Theorem star_e k : forall p, (p < Nat.pow 2 k)%nat ->
  conjugate k (basis k p) = if Nat.eqb p 0 then basis k p else scale k neg_one (basis k p).
Proof.
  induction k as [|j IH]; intros p Hp.
  - cbn in Hp. assert (p = O) as -> by lia. reflexivity.
  - destruct (Nat.ltb_spec p (Nat.pow 2 j)) as [Hl | Hl].
    + rewrite (basis_low j p Hl). cbn [conjugate fst snd]. rewrite IH by exact Hl. rewrite scale_zero.
      destruct (Nat.eqb p 0); [reflexivity |]. cbn [scale fst snd]. rewrite scale_zero. reflexivity.
    + destruct (CdTowerBasisSign.split_high j p Hp Hl) as [c [Hc ->]].
      rewrite (basis_high j c Hc), high_nonzero. cbn [conjugate scale fst snd].
      rewrite conj_zero, scale_zero. reflexivity.
Qed.

Definition unit_conj (a : nat) : D.t := if Nat.eqb a 0 then D.one else neg_one.

Lemma conj_basis k p : (p < Nat.pow 2 k)%nat -> conjugate k (basis k p) = scale k (unit_conj p) (basis k p).
Proof.
  intro Hp. rewrite star_e by exact Hp. unfold unit_conj.
  destruct (Nat.eqb p 0); [symmetry; apply scale_one | reflexivity].
Qed.

Definition ring_sign (k p q : nat) : D.t := if neg_sign k p q then neg_one else D.one.

Ltac destruct_signs :=
  repeat match goal with |- context [neg_sign ?a ?b ?c] => destruct (neg_sign a b c) end.

Lemma basis_mul_ring_sign k : forall p q, (p < Nat.pow 2 k)%nat -> (q < Nat.pow 2 k)%nat ->
  mul k (basis k p) (basis k q) = scale k (ring_sign k p q) (basis k (Nat.lxor p q)).
Proof.
  induction k as [|j IH]; intros p q Hp Hq.
  - cbn in Hp, Hq. assert (p = O) as -> by lia. assert (q = O) as -> by lia.
    cbn. unfold ring_sign. cbn. ring.
  - destruct (mul_zero j) as [Zl Zr]. unfold ring_sign. rewrite neg_sign_unfold.
    destruct (Nat.ltb_spec p (Nat.pow 2 j)) as [Hpl | Hpl];
      [rewrite (basis_low j p Hpl)
      | destruct (CdTowerBasisSign.split_high j p Hp Hpl) as [p' [Hp' ->]];
        rewrite (basis_high j p' Hp')];
    (destruct (Nat.ltb_spec q (Nat.pow 2 j)) as [Hql | Hql];
      [rewrite (basis_low j q Hql)
      | destruct (CdTowerBasisSign.split_high j q Hq Hql) as [q' [Hq' ->]];
        rewrite (basis_high j q' Hq')]);
    rewrite ?Nat.add_sub.
    1: rewrite basis_low by (apply CdTowerBasisSign.lxor_lt; assumption).
    2: rewrite CdTowerBasisSign.lxor_high_r, basis_high
         by (try apply CdTowerBasisSign.lxor_lt; assumption).
    3: rewrite CdTowerBasisSign.lxor_high_l, basis_high
         by (try apply CdTowerBasisSign.lxor_lt; assumption).
    4: rewrite CdTowerBasisSign.lxor_high_lr, basis_low
         by (try apply CdTowerBasisSign.lxor_lt; assumption).
    all: cbn [mul scale fst snd]; rewrite ?conj_zero, ?conj_basis by assumption;
      rewrite ?mul_scale_l, ?mul_scale_r, ?Zl, ?Zr, ?IH by assumption; unfold ring_sign, unit_conj.
    4: rewrite (Nat.lxor_comm q' p'); destruct (Nat.eqb_spec q' 0) as [-> | _];
      [rewrite neg_sign_zero_l |].
    3: destruct (Nat.eqb q 0).
    all: destruct_signs; cbn [xorb negb]; f_equal; vec.
Qed.

(** Tower.e_mul_e: e_p e_q = -e_(p XOR q) when neg_sign k p q holds and
    e_(p XOR q) otherwise. *)
Theorem e_mul_e k p q : (p < Nat.pow 2 k)%nat -> (q < Nat.pow 2 k)%nat ->
  mul k (basis k p) (basis k q) =
  if neg_sign k p q then scale k neg_one (basis k (Nat.lxor p q)) else basis k (Nat.lxor p q).
Proof.
  intros Hp Hq. rewrite basis_mul_ring_sign by assumption. unfold ring_sign.
  destruct (neg_sign k p q); [reflexivity | apply scale_one].
Qed.

Lemma h_sign k p q : H.h (sign k p q) = ring_sign k p q.
Proof.
  unfold sign, ring_sign, neg_one. destruct (neg_sign k p q).
  - change (-1)%Z with (IntegerRing.opp IntegerRing.one). rewrite H.h_opp, H.h_one. reflexivity.
  - change 1%Z with IntegerRing.one. apply H.h_one.
Qed.

(** Tower.e_mul_e_sign: e_p e_q = sign(p, q) e_(p XOR q), the integer
    sign acting through the ring map from the integers. *)
Theorem e_mul_e_sign k p q : (p < Nat.pow 2 k)%nat -> (q < Nat.pow 2 k)%nat ->
  mul k (basis k p) (basis k q) = scale k (H.h (sign k p q)) (basis k (Nat.lxor p q)).
Proof. intros Hp Hq. rewrite h_sign. apply basis_mul_ring_sign; assumption. Qed.

(** Tower.e_mul_self: every basis vector other than 1 squares to -1. *)
Theorem e_mul_self k p : (p < Nat.pow 2 k)%nat -> p <> O ->
  mul k (basis k p) (basis k p) = scale k neg_one (one k).
Proof.
  intros Hp Hp0. rewrite e_mul_e, neg_sign_self, Nat.lxor_nilpotent, basis_zero by assumption.
  reflexivity.
Qed.

(** Tower.e_mul_e_anticomm: two distinct basis vectors other than 1
    anticommute. *)
Theorem e_mul_e_anticomm k p q : (p < Nat.pow 2 k)%nat -> (q < Nat.pow 2 k)%nat ->
  p <> O -> q <> O -> p <> q ->
  mul k (basis k q) (basis k p) = scale k neg_one (mul k (basis k p) (basis k q)).
Proof.
  intros Hp Hq Hp0 Hq0 Hpq. rewrite !e_mul_e by assumption.
  rewrite (neg_sign_swap k p q Hp Hq Hp0 Hq0 Hpq), (Nat.lxor_comm q p).
  destruct (neg_sign k p q); cbn [negb]; [symmetry; apply scale_neg_neg | reflexivity].
Qed.

End TowerBasisBridge.

Module IntegerTowerBasisBridge := TowerBasisBridge IntegerRing.

(** At level 3 over the integers, e_3 e_5 = -e_6 and e_5 e_3 = e_6: the
    entries (3, 5) and (5, 3) of Lean's Tower.sign 3. *)
Example integer_e3_e5 :
  IntegerTowerBasisBridge.B.T.mul 3 (IntegerTowerBasisBridge.B.basis 3 3) (IntegerTowerBasisBridge.B.basis 3 5) =
    IntegerTowerBasisBridge.B.T.scale 3 (-1)%Z (IntegerTowerBasisBridge.B.basis 3 6) /\
  IntegerTowerBasisBridge.B.T.mul 3 (IntegerTowerBasisBridge.B.basis 3 5) (IntegerTowerBasisBridge.B.basis 3 3) =
    IntegerTowerBasisBridge.B.basis 3 6 /\
  TowerSign.sign 3 3 5 = (-1)%Z /\ TowerSign.sign 3 5 3 = 1%Z.
Proof. vm_compute. repeat split. Qed.
