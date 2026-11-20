(** The first and second half of the kernel of left multiplication: the Rocq bridge of the Lean module
    lean/GororobaMath/CayleyDickson/HalfFold.lean.

    Convention: the tower, product and conjugation of CdTowerDomain.v,
    (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)), with the identity as the conjugation of the coefficients.
    The Lean tower has the same product; the Lean zero is zero k.

    The functor HalfFoldBridge restates each headline theorem of the Lean module at the coefficient ring D,
    with the Rocq statement of its source theorem:

    - first_half is Tower.mk_left_mul_eq_zero_iff.
    - second_half is Tower.mk_right_mul_eq_zero_iff.

    The Rocq statements are narrower than the Lean ones: the coefficients form an ordered domain whose conjugation is the identity
    (the signature OrderedDomain), where Lean takes a commutative ring with the identity as star and the ordered section of its module.
    IntegerHalfFoldBridge instantiates the functor at the integers. *)

Require Import CdTowerDomain CdHalfFold.

Module HalfFoldBridge (D : OrderedDomain).
Module H := HalfFold D.
Import H H.T.

Theorem first_half k (a c d : cd k) :
    mul (S k) (a, zero k) (c, d) = zero (S k) <-> mul k a c = zero k /\ mul k a d = zero k.
Proof. apply H.first_half. Qed.

Theorem second_half k (b c d : cd k) :
    mul (S k) (zero k, b) (c, d) = zero (S k) <-> mul k b c = zero k /\ mul k b d = zero k.
Proof. apply H.second_half. Qed.

End HalfFoldBridge.

Module IntegerHalfFoldBridge := HalfFoldBridge ZDomain.
