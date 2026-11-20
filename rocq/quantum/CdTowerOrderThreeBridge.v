(** The order-three map of level 4 over a ring with a square root of 3: the Rocq bridge of the Lean module
    lean/GororobaMath/CayleyDickson/OrderThree.lean.

    Convention: the tower, product and conjugation of CdTowerRing.v,
    (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)) and conj (a, b) = (conj a, -b), with the identity as the
    conjugation of the coefficients. The Lean tower has the same product and star; the Lean negation -x is
    scale k neg_one x, the Lean zero is zero k, and the Lean basis element e R k p is basis k i at the
    index i of the bit vector p.
    psi2 is Lean's Tower.orderThree at the square root r3 = D.r3 of 3.

    The functor OrderThreeBridge restates each headline theorem of the Lean module at the coefficient ring D,
    with the Rocq statement of its source theorem:

    - psi2_mul is Tower.orderThree_mul.
    - psi2_conj is Tower.orderThree_star.

    Substituted values: R := D with the identity as star, r3 := D.r3 with r3 * r3 = 3 (the axiom r3_squared), and the level 4 of psi2_mul.

    The Rocq statements are those of the Lean module: the coefficients form a commutative ring with a square root of 3
    (the signature RingWithRoot3) whose conjugation is the identity. ci/compare_order_three.sh compares Tower.orderThree with psi2.
    Root3OrderThreeBridge instantiates the functor at the integers adjoined a square root of 3. *)

Require Import CdTowerRing CdTowerRingBasis CdTowerRingBaseChange CdTowerOrderThreeMap.

Module OrderThreeBridge (D : RingWithRoot3).
Module M := OrderThreeMap D.
Import M M.BC.

Theorem psi2_mul : forall x y, TB.mul 4 (psi2 3 x) (psi2 3 y) = TB.scale 4 TB.two (psi2 3 (TB.mul 4 x y)).
Proof. apply M.psi2_mul. Qed.

Theorem psi2_conj k x : psi2 k (TB.conjugate (S k) x) = TB.conjugate (S k) (psi2 k x).
Proof. apply M.psi2_conj. Qed.

End OrderThreeBridge.

Module Root3OrderThreeBridge := OrderThreeBridge Root3Integers.
