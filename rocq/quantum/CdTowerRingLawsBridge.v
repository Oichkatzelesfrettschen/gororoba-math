(** The kernel laws of the commutative-ring pair tower: the Rocq bridge of the Lean module
    lean/GororobaMath/CayleyDickson/RingLaws.lean.

    Convention: the tower, product and conjugation of CdTowerRing.v,
    (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)) and conj (a, b) = (conj a, -b), with the identity as the
    conjugation of the coefficients. The Lean tower has the same product and star; the Lean negation -x is
    scale k neg_one x, the Lean zero is zero k, and the Lean hypothesis star a = -a is pure k a.

    The functor RingLawsBridge restates each headline theorem of the Lean module at the coefficient ring D,
    with the Rocq statement of its source theorem:

    - kernel_conj is Tower.mul_eq_zero_iff_star_mul_star.
    - pure_kernel_conj is Tower.mul_eq_zero_iff_star_mul_of_star_eq_neg.
    - reflect_kernel is Tower.mul_eq_zero_iff_reflect_mul_reflect.

    Substituted values: R := D, the star of R the identity, the level k the Rocq k, and the Lean zero, negation and pure predicate as stated above.

    The Rocq statements are narrower than the Lean ones: the coefficients form a commutative ring whose conjugation is the identity
    (the signature CommutativeRing), where Lean takes every NonAssocRing with a StarRing.
    IntegerRingLawsBridge instantiates the functor at the integers. *)

Require Import CdTowerRing CdTowerDomain.

Module RingLawsBridge (D : CommutativeRing).
Module T := RingTower D.
Import T.

Theorem kernel_conj k a z : mul k a z = zero k <-> mul k (conjugate k z) (conjugate k a) = zero k.
Proof. apply T.kernel_conj. Qed.

Theorem pure_kernel_conj k a z : pure k a -> (mul k a z = zero k <-> mul k (conjugate k z) a = zero k).
Proof. apply T.pure_kernel_conj. Qed.

Theorem reflect_kernel k x z :
  mul (S k) x z = zero (S k) <-> mul (S k) (reflect k x) (reflect k z) = zero (S k).
Proof. apply T.reflect_kernel. Qed.

End RingLawsBridge.

Module IntegerRingLawsBridge := RingLawsBridge ZDomain.
