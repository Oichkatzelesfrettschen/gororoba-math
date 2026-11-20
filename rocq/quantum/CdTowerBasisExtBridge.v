(** Maps determined by their values on the basis: the Rocq bridge of the Lean module
    lean/GororobaMath/CayleyDickson/BasisExt.lean.

    Convention: the tower, product and conjugation of CdTowerRing.v,
    (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)) and conj (a, b) = (conj a, -b), with the identity as the
    conjugation of the coefficients. The Lean tower has the same product and star; the Lean negation -x is
    scale k neg_one x, the Lean zero is zero k, and the Lean basis element e R k p is basis k i at the
    index i of the bit vector p.

    The functor BasisExtBridge restates each headline theorem of the Lean module at the coefficient ring D,
    with the Rocq statement of its source theorem:

    - multiplicative_by_basis is Tower.map_mul_of_map_e_mul_e.
    - derivation_by_basis is Tower.leibniz_of_leibniz_e.

    Substituted values: R := D with the identity as star, the Lean linear map f the Rocq map f with the hypothesis linear k f, and a BitVec index p the natural number i below 2^k.

    The Rocq statements are narrower than the Lean ones: indices i, j below 2^k, where Lean takes bit vectors of width k, and the coefficients form a commutative ring
    whose conjugation is the identity (the signature CommutativeRing), as in Lean.
    IntegerBasisExtBridge instantiates the functor at the integers. *)

Require Import CdTowerRing CdTowerRingBasis CdTowerDomain.

Module BasisExtBridge (D : CommutativeRing).
Module B := RingTowerBasis D.
Import B B.T.

Theorem multiplicative_by_basis k f : linear k f ->
  (forall i j, (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat ->
     f (mul k (basis k i) (basis k j)) = mul k (f (basis k i)) (f (basis k j))) ->
  forall x y, f (mul k x y) = mul k (f x) (f y).
Proof. apply B.multiplicative_by_basis. Qed.

Theorem derivation_by_basis k f : linear k f ->
  (forall i j, (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat ->
     f (mul k (basis k i) (basis k j)) =
     add k (mul k (f (basis k i)) (basis k j)) (mul k (basis k i) (f (basis k j)))) ->
  forall x y, f (mul k x y) = add k (mul k (f x) y) (mul k x (f y)).
Proof. apply B.derivation_by_basis. Qed.

End BasisExtBridge.

Module IntegerBasisExtBridge := BasisExtBridge ZDomain.
