(** Transport of a basis-defined map along a ring homomorphism: the Rocq bridge of the Lean module
    lean/GororobaMath/CayleyDickson/BaseChange.lean.

    Convention: the tower, product and conjugation of CdTowerRing.v,
    (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)) and conj (a, b) = (conj a, -b), with the identity as the
    conjugation of the coefficients. The Lean tower has the same product and star; the Lean negation -x is
    scale k neg_one x, the Lean zero is zero k, and the Lean basis element e R k p is basis k i at the
    index i of the bit vector p.

    The functor BaseChangeBridge restates each headline theorem of the Lean module at the coefficient ring D,
    with the Rocq statement of its source theorem:

    - scaled_multiplicative_transport is Tower.baseChange_mul.
    - derivation_transport is Tower.baseChange_leibniz.

    Substituted values: R := A, S := B and phi := H.h, the Lean linear map F the map source_map k images of the list images of its values, and c an element of A.

    The Rocq statements are narrower than the Lean ones: the map F is given by the list images of its values on the source basis, where Lean takes an R-linear map F, and
    indices below 2^k stand for bit vectors of width k.
    IntegerBaseChangeBridge instantiates the functor at the base change from the integers to the integers. *)

Require Import CdTowerRing CdTowerRingBasis CdTowerRingBaseChange CdTowerDomain.

Module BaseChangeBridge (A B : CommutativeRing) (H : RingHom A B).
Module BC := BaseChange A B H.
Import BC.

Theorem scaled_multiplicative_transport k images c :
  (forall i j, (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat ->
     TA.mul k (source_map k images (SA.basis k i)) (source_map k images (SA.basis k j)) =
     TA.scale k c (source_map k images (TA.mul k (SA.basis k i) (SA.basis k j)))) ->
  forall x y, TB.mul k (target_map k images x) (target_map k images y) =
              TB.scale k (H.h c) (target_map k images (TB.mul k x y)).
Proof. apply BC.scaled_multiplicative_transport. Qed.

Theorem derivation_transport k images :
  (forall i j, (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat ->
     source_map k images (TA.mul k (SA.basis k i) (SA.basis k j)) =
     TA.add k (TA.mul k (source_map k images (SA.basis k i)) (SA.basis k j))
              (TA.mul k (SA.basis k i) (source_map k images (SA.basis k j)))) ->
  forall x y, target_map k images (TB.mul k x y) =
              TB.add k (TB.mul k (target_map k images x) y) (TB.mul k x (target_map k images y)).
Proof. apply BC.derivation_transport. Qed.

End BaseChangeBridge.

Module IntegerToIntegerHom := IntegerHom ZDomain.
Module IntegerBaseChangeBridge := BaseChangeBridge IntegerRing ZDomain IntegerToIntegerHom.
