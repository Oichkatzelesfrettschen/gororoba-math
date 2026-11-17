(** The coordinates of the commutative-ring pair tower in its basis: the
    Rocq bridge of the two headline theorems of the Lean module
    lean/GororobaMath/CayleyDickson/TowerModule.lean.

    Convention: the tower, product and basis of CdTowerRing.v and
    CdTowerRingBasis.v, (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)),
    with basis k i the basis vector of index i below 2^k, whose top index
    bit selects the second half of the pair; CdTowerBasisBridge.v ties
    basis k i to Lean's e R k p at the bit vector p of value i, makes
    Nat.lxor the index of p ^^^ q, and makes TowerSign.neg_sign Lean's
    Tower.negSign with the same argument order. The scalar action of Lean's
    Tower.instModule is scale k, the sum of a finite family is tsum k n,
    and the coordinate (Tower.basis R k).repr x p of Lean is coord k x i
    at the value i of p (coord_basis of CdTowerRingBasis.v is Lean's
    Tower.repr_e).

    The functor TowerModuleBridge restates the two headline theorems at
    the coefficient ring D:

    - free_basis_pow2 is the reading of Tower.finrank_eq that the Rocq
      library carries: the 2^k vectors basis k i, i below 2^k, form a
      basis of level k. Every vector is the combination of the basis with
      its coordinates (decompose of CdTowerRingBasis.v), the coordinates
      of a combination are its coefficients (coord_combination), so the
      coordinate map is the inverse of the combination map, and a
      combination that vanishes has every coefficient zero.
    - repr_e_mul is Tower.repr_e_mul, for i and w below 2^k: the
      coordinate of e_i y at w is the coordinate of y at i XOR w, negated
      when neg_sign k i (i XOR w) holds.

    The proof of repr_e_mul decomposes y in the basis, applies
    basis_mul_ring_sign of CdTowerBasisBridge.v (the lemma behind its
    e_mul_e) to each term, and keeps the one term of index
    i XOR w. basis_mul_coord of CdTowerBasisSign.v states the same
    coordinates over the integer tower of CdImaginarySumConference.v,
    a type of its own, with sigma in place of neg_sign.

    The Rocq statements are narrower than the Lean ones. repr_e_mul takes
    an index as a nat below 2^k, where Lean takes a BitVec k; its
    coefficient ring is the same, a commutative ring whose star is the
    identity. free_basis_pow2 states one basis of 2^k vectors, where Lean's
    finrank is the size of every basis over a nontrivial commutative ring;
    that invariance (the invariant basis number property of a commutative
    ring) has no statement in Stdlib, and the Rocq statement also holds
    over the zero ring, where Lean's Nontrivial hypothesis excludes it. Its
    conjugation is the identity, where Lean takes every StarRing.
    IntegerTowerModuleBridge instantiates the functor at the integers, and
    integer_repr_e3_mul evaluates two coordinates of level 3 there. *)

From Stdlib Require Import Ring Lia PeanoNat ZArith List.
Require Import CdTowerRing CdTowerRingBasis CdTowerRingBaseChange.
Require CdTowerBasisSign.
Require Import CdTowerBasisBridge.

Module TowerModuleBridge (D : CommutativeRing).
Module BB := TowerBasisBridge D.
Import BB BB.B BB.B.T TowerSign.
Add Ring tower_module_bridge_ring : D.ring_th.

(** The coordinate j of the combination of the basis with coefficients c
    is c j. *)
Lemma coord_combination k c j : (j < Nat.pow 2 k)%nat ->
  coord k (tsum k (Nat.pow 2 k) (fun i => scale k (c i) (basis k i))) j = c j.
Proof.
  intro Hj. rewrite coord_tsum.
  rewrite (dsum_ext _ _ (fun i => D.mul (c i) (if Nat.eqb i j then D.one else D.zero))).
  - rewrite dsum_delta, (proj2 (Nat.ltb_lt _ _) Hj). reflexivity.
  - intros m Hm. rewrite coord_scale, coord_basis by assumption. reflexivity.
Qed.

(** Tower.finrank_eq, read as a basis of 2^k vectors: spanning with the
    coordinates as coefficients, coordinates of a combination equal to its
    coefficients, and linear independence. *)
Theorem free_basis_pow2 k :
  (forall x, x = tsum k (Nat.pow 2 k) (fun i => scale k (coord k x i) (basis k i))) /\
  (forall c j, (j < Nat.pow 2 k)%nat ->
     coord k (tsum k (Nat.pow 2 k) (fun i => scale k (c i) (basis k i))) j = c j) /\
  (forall c, tsum k (Nat.pow 2 k) (fun i => scale k (c i) (basis k i)) = zero k ->
     forall i, (i < Nat.pow 2 k)%nat -> c i = D.zero).
Proof.
  split; [apply decompose |]. split; [intros c j; apply coord_combination |].
  intros c E i Hi. rewrite <- (coord_combination k c i Hi), E. apply coord_zero.
Qed.

Lemma lxor_eqb_shift i m w : Nat.eqb (Nat.lxor i m) w = Nat.eqb m (Nat.lxor i w).
Proof.
  destruct (Nat.eqb_spec (Nat.lxor i m) w) as [E | E], (Nat.eqb_spec m (Nat.lxor i w)) as [F | F];
    try reflexivity.
  - exfalso. apply F. rewrite <- E, <- Nat.lxor_assoc, Nat.lxor_nilpotent, Nat.lxor_0_l. reflexivity.
  - exfalso. apply E. rewrite F, <- Nat.lxor_assoc, Nat.lxor_nilpotent, Nat.lxor_0_l. reflexivity.
Qed.

(** Tower.repr_e_mul: left multiplication by e_i is a signed permutation
    of coordinates. *)
Theorem repr_e_mul k i w y : (i < Nat.pow 2 k)%nat -> (w < Nat.pow 2 k)%nat ->
  coord k (mul k (basis k i) y) w =
  if neg_sign k i (Nat.lxor i w) then D.opp (coord k y (Nat.lxor i w)) else coord k y (Nat.lxor i w).
Proof.
  intros Hi Hw. pose proof (CdTowerBasisSign.lxor_lt k i w Hi Hw) as Hiw.
  assert (Ey : mul k (basis k i) y =
    mul k (basis k i) (tsum k (Nat.pow 2 k) (fun m => scale k (coord k y m) (basis k m))))
    by (f_equal; apply decompose).
  rewrite Ey, (linear_tsum k (mul k (basis k i)) _ _ (proj2 (mul_bilinear k) (basis k i))), coord_tsum.
  rewrite (dsum_ext _ _ (fun m => D.mul (D.mul (coord k y m) (ring_sign k i m))
    (if Nat.eqb m (Nat.lxor i w) then D.one else D.zero))).
  - rewrite dsum_delta, (proj2 (Nat.ltb_lt _ _) Hiw). unfold ring_sign, neg_one.
    destruct (neg_sign k i (Nat.lxor i w)); ring.
  - intros m Hm. pose proof (CdTowerBasisSign.lxor_lt k i m Hi Hm) as Him.
    rewrite mul_scale_r, coord_scale, basis_mul_ring_sign, coord_scale, coord_basis, lxor_eqb_shift
      by assumption.
    ring.
Qed.

End TowerModuleBridge.

Module IntegerTowerModuleBridge := TowerModuleBridge IntegerRing.

(** At level 3 over the integers, with y the combination of e_0, ..., e_7
    with coefficients 1, ..., 8: the coordinate of e_3 y at 6 is minus the
    coordinate of y at 3 XOR 6 = 5, which is 6, since e_3 e_5 = -e_6
    (integer_e3_e5 of CdTowerBasisBridge.v, the entry (3, 5) of Lean's
    Tower.sign 3); the coordinate at 2 is the coordinate of y at 3 XOR 2 = 1,
    which is 2, since e_3 e_1 = e_2. *)
Example integer_repr_e3_mul :
  let y := IntegerTowerModuleBridge.BB.B.tsum 3 8
    (fun i => IntegerTowerModuleBridge.BB.B.T.scale 3 (Z.of_nat (S i)) (IntegerTowerModuleBridge.BB.B.basis 3 i)) in
  IntegerTowerModuleBridge.BB.B.T.coord 3
    (IntegerTowerModuleBridge.BB.B.T.mul 3 (IntegerTowerModuleBridge.BB.B.basis 3 3) y) 6 = (-6)%Z /\
  IntegerTowerModuleBridge.BB.B.T.coord 3
    (IntegerTowerModuleBridge.BB.B.T.mul 3 (IntegerTowerModuleBridge.BB.B.basis 3 3) y) 2 = 2%Z /\
  TowerSign.neg_sign 3 3 5 = true /\ TowerSign.neg_sign 3 3 1 = false.
Proof. vm_compute. repeat split. Qed.
