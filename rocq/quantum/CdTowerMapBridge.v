(** Maps of the doubling and the iterated embedding: the Rocq bridge of the Lean module
    lean/GororobaMath/CayleyDickson/Map.lean.

    Convention: the tower, product and conjugation of CdTowerRing.v,
    (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)) and conj (a, b) = (conj a, -b), with the identity as the
    conjugation of the coefficients. The Lean tower has the same product and star; the Lean negation -x is
    scale k neg_one x, the Lean zero is zero k, and the Lean basis element e R k p is basis k i at the
    index i of the bit vector p.

    The functor MapBridge restates each headline theorem of the Lean module at the coefficient ring D,
    with the Rocq statement of its source theorem:

    - diag_mul is CayleyDickson.map_mul, for an endomap f of level k.
    - lift_mul is Tower.lift_mul, with the level k + j in place of j + k.
    - lift_injective is Tower.lift_injective, with the level k + j in place of j + k.

    The Rocq statements are narrower than the Lean ones: the coefficients form a commutative ring whose conjugation is the identity
    (the signature CommutativeRing), where Lean takes every NonAssocRing with a StarRing; diag_mul takes an endomap of one level
    that preserves sums, scalars, products and conjugates, where Lean takes a non-unital ring homomorphism between two star rings
    that commutes with the star.
    IntegerMapBridge instantiates the functor at the integers. *)

Require Import CdTowerRing CdTowerDomain.

Module MapBridge (D : CommutativeRing).
Module T := RingTower D.
Import T.

Theorem diag_mul k (f : cd k -> cd k)
  (f_add : forall x y, f (add k x y) = add k (f x) (f y))
  (f_scale : forall r x, f (scale k r x) = scale k r (f x))
  (f_mul : forall x y, f (mul k x y) = mul k (f x) (f y))
  (f_conj : forall x, f (conjugate k x) = conjugate k (f x)) x y :
  diag k f (mul (S k) x y) = mul (S k) (diag k f x) (diag k f y).
Proof. exact (T.diag_mul k f f_add f_scale f_mul f_conj x y). Qed.

Theorem lift_mul j k x y : mul (k + j) (lift j k x) (lift j k y) = lift j k (mul j x y).
Proof. apply T.lift_mul. Qed.

Theorem lift_injective j k x y : lift j k x = lift j k y -> x = y.
Proof. apply T.lift_injective. Qed.

End MapBridge.

Module IntegerMapBridge := MapBridge ZDomain.
