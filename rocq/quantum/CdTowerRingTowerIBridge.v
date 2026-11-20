(** The kernel swap of the pair tower over a ring with a square root of -1: the Rocq bridge of the Lean module
    lean/GororobaMath/CayleyDickson/RingTowerI.lean.

    Convention: the tower, product and conjugation of CdTowerRing.v,
    (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)) and conj (a, b) = (conj a, -b), with the identity as the
    conjugation of the coefficients. The Lean tower has the same product and star; the Lean negation -x is
    scale k neg_one x, the Lean zero is zero k, and the Lean basis element e R k p is basis k i at the
    index i of the bit vector p.

    The functor RingTowerIBridge restates each headline theorem of the Lean module at the coefficient ring D,
    with the Rocq statement of its source theorem:

    - kernel_swap_iff_two_zero is Tower.kernel_swap_iff_two_eq_zero.
    - pure_kernel_swap_two_zero is Tower.pure_kernel_swap_two_eq_zero.

    The Rocq statements are those of the Lean module: the coefficients form a commutative ring with a square root i of -1
    whose conjugation is the identity (the signature CommutativeRingWithI), and D.i is the Lean i.
    mod5_kernel_swap_fails of CdTowerRing.v is the Lean zmod5_not_pure_kernel_swap, over the integers modulo 5.
    GaussianRingTowerIBridge instantiates the functor at the Gaussian integers. *)

Require Import CdTowerRing.

Module RingTowerIBridge (D : CommutativeRingWithI).
Module R := RingTowerI D.
Import R.

Theorem kernel_swap_iff_two_zero k :
  (forall a z, T.mul (k + 2) a z = T.zero (k + 2) -> T.mul (k + 2) z a = T.zero (k + 2)) <-> T.two = D.zero.
Proof. apply R.kernel_swap_iff_two_zero. Qed.

Theorem pure_kernel_swap_two_zero k :
  (forall a z, T.pure (k + 2) a -> T.mul (k + 2) a z = T.zero (k + 2) -> T.mul (k + 2) z a = T.zero (k + 2)) ->
  T.two = D.zero.
Proof. apply R.pure_kernel_swap_two_zero. Qed.

End RingTowerIBridge.

Module GaussianRingTowerIBridge := RingTowerIBridge GaussianIntegers.
