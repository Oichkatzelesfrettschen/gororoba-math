(** Non-associativity of the commutative-ring pair tower at every level
    from the octonions on: the Rocq bridge of the Lean module
    lean/GororobaMath/CayleyDickson/NonAssociative.lean.

    Convention: the tower, product and basis of CdTowerRing.v and
    CdTowerRingBasis.v, (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)),
    with basis k i the basis vector of index i below 2^k, whose top index
    bit selects the second half of the pair. The Lean tower has the same
    product, and its basis element e R k p, for p : BitVec k, lies in the
    second half exactly when the most significant bit of p is set, so
    basis k i is e R k p at the bit vector p of value i.

    The functor NonAssociative restates each theorem of the Lean module at
    the coefficient ring D:

    - embed_mul_bridge is Tower.mk_zero_mul_mk_zero.
    - basis_neq_neg is Tower.e_ne_neg_e, for i below 2^k.
    - octonion_e1_e2_e4_left and octonion_e1_e2_e4_right name the two
      products (e_1 e_2) e_4 = e_7 and e_1 (e_2 e_4) = -e_7, and
      octonion_e1_e2_e4_mul_assoc_ne is
      Tower.octonion_e1_e2_e4_mul_assoc_ne.
    - exists_mul_assoc_ne is Tower.exists_mul_assoc_ne, and
      exists_mul_assoc_ne_level_seven is
      Tower.exists_mul_assoc_ne_level_seven.

    The hypothesis 2 <> 0 of the Lean theorems is the hypothesis two <>
    D.zero here. The Rocq statements are narrower than the Lean ones: the
    coefficients form a commutative ring whose conjugation is the identity
    (the signature CommutativeRing), where Lean takes every NonAssocRing
    with a StarRing. IntegerNonAssociative instantiates the functor at the
    integers, where 2 differs from 0. *)

From Stdlib Require Import Ring Lia PeanoNat ZArith.
Require Import CdTowerRing CdTowerRingBasis CdTowerRingBaseChange.

Module NonAssociative (D : CommutativeRing).
Module B := RingTowerBasis D.
Import B B.T.
Add Ring nonassociative_ring : D.ring_th.

Theorem embed_mul_bridge k (a c : cd k) :
  mul (S k) (a, zero k) (c, zero k) = (mul k a c, zero k).
Proof. apply embed_mul. Qed.

Theorem basis_neq_neg (H2 : two <> D.zero) k i :
  (i < Nat.pow 2 k)%nat -> basis k i <> scale k neg_one (basis k i).
Proof.
  intros Hi E.
  pose proof (f_equal (fun v => coord k v i) E) as C. cbn beta in C.
  rewrite coord_scale, coord_basis, Nat.eqb_refl in C by exact Hi.
  apply H2. unfold two. rewrite C at 2. unfold neg_one. ring.
Qed.

Ltac pair_ring :=
  repeat match goal with |- (_, _) = (_, _) => f_equal end; unfold neg_one; ring.

Theorem octonion_e1_e2_e4_left :
  mul 3 (mul 3 (basis 3 1) (basis 3 2)) (basis 3 4) = basis 3 7.
Proof. cbn. pair_ring. Qed.

Theorem octonion_e1_e2_e4_right :
  mul 3 (basis 3 1) (mul 3 (basis 3 2) (basis 3 4)) = scale 3 neg_one (basis 3 7).
Proof. cbn. pair_ring. Qed.

Theorem octonion_e1_e2_e4_mul_assoc_ne (H2 : two <> D.zero) :
  mul 3 (mul 3 (basis 3 1) (basis 3 2)) (basis 3 4) <>
  mul 3 (basis 3 1) (mul 3 (basis 3 2) (basis 3 4)).
Proof.
  rewrite octonion_e1_e2_e4_left, octonion_e1_e2_e4_right.
  apply (basis_neq_neg H2 3 7). cbn. lia.
Qed.

Theorem exists_mul_assoc_ne (H2 : two <> D.zero) k :
  (3 <= k)%nat -> exists a b c : cd k, mul k (mul k a b) c <> mul k a (mul k b c).
Proof.
  intro Hk. replace k with ((k - 3) + 3)%nat by lia.
  exists (lift 3 (k - 3) (basis 3 1)), (lift 3 (k - 3) (basis 3 2)), (lift 3 (k - 3) (basis 3 4)).
  rewrite !lift_mul. intro E. apply lift_injective in E.
  exact (octonion_e1_e2_e4_mul_assoc_ne H2 E).
Qed.

Theorem exists_mul_assoc_ne_level_seven (H2 : two <> D.zero) :
  exists a b c : cd 7, mul 7 (mul 7 a b) c <> mul 7 a (mul 7 b c).
Proof. apply (exists_mul_assoc_ne H2). lia. Qed.

End NonAssociative.

Module IntegerNonAssociative := NonAssociative IntegerRing.

Theorem integer_two_neq_zero : IntegerNonAssociative.B.T.two <> IntegerRing.zero.
Proof. intro H. cbv in H. discriminate H. Qed.

Theorem integer_exists_mul_assoc_ne_level_seven :
  exists a b c : IntegerNonAssociative.B.T.cd 7,
    IntegerNonAssociative.B.T.mul 7 (IntegerNonAssociative.B.T.mul 7 a b) c <>
    IntegerNonAssociative.B.T.mul 7 a (IntegerNonAssociative.B.T.mul 7 b c).
Proof. exact (IntegerNonAssociative.exists_mul_assoc_ne_level_seven integer_two_neq_zero). Qed.
