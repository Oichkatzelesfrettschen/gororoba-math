(** The certificate of the 14 sedenion derivation tables: the Rocq bridge of the Lean theorem
    Tower.finrank_leibniz_of_certificate of lean/GororobaMath/CayleyDickson/Derivation.lean.

    Convention: the tower, product and conjugation of CdTowerRing.v,
    (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)) and conj (a, b) = (conj a, -b), with the identity as the
    conjugation of the coefficients. The Lean tower has the same product and star; the Lean zero is zero k,
    the Lean sum over Fin 14 is SB.tsum 4 14, and the Lean scalar action d • x is TB.scale 4 d x.

    The functor G2DerivationBridge states, over a commutative ring D with a square root of -1, the three
    hypotheses of Tower.finrank_leibniz_of_certificate with the substituted values
    K := D, k := 4, n := 14, T t := target_map 4 (table t), the map of the table images_(t+1) of
    CdTowerG2Derivations.v carried to D by the homomorphism (a, b) -> a + b i of GaussianIntegerHom.v, and
    d := h(6), the scalar of CdTowerG2DerivationSpan.v:
    - hT, each T t satisfies the Leibniz rule on all of level 4 (derivation_1 to derivation_14, each the
      instance phi := h, k := 4, F := the map of images_(t+1) of Tower.baseChange_leibniz of
      lean/GororobaMath/CayleyDickson/BaseChange.lean);
    - hind, a combination of the T t that vanishes everywhere has every coefficient zero
      (derivations_independent);
    - hspan, for every linear F that satisfies the Leibniz rule, h(6) F is a combination of the T t
      (derivations_spanned).
    LinearIndependent K T reads as the second clause and membership of d • F in the span of the T t as the
    existence of 14 coefficients.

    The Rocq statement is narrower than the Lean one: it holds the hypotheses and not the conclusion,
    since Rocq holds no dimension of a module; the Lean theorem gives finrank = 14 for the derivations of
    level 4 over a field D with a square root of -1 in which 6 is nonzero (its hypothesis hd). Over the reals
    no such i exists, and the clauses say nothing about the dimension there.
    GaussianG2DerivationBridge instantiates the functor at the Gaussian integers. *)

From Stdlib Require Import Lia.
Require Import CdTowerRing CdTowerRingBasis CdTowerRingBaseChange GaussianIntegerHom.
Require Import CdTowerG2Derivations CdTowerG2DerivationSpan.

Module G2DerivationBridge (D : CommutativeRingWithI).
Module H := GaussianHom D.
Module G := G2Derivations D H.
Module S := G2DerivationSpan D H.
Import S.LS.BC.

Theorem derivation_dimension_certificate :
  (forall t, (t < 14)%nat -> forall x y,
     target_map 4 (S.table t) (TB.mul 4 x y) =
     TB.add 4 (TB.mul 4 (target_map 4 (S.table t) x) y) (TB.mul 4 x (target_map 4 (S.table t) y))) /\
  (forall a : nat -> D.t,
     (forall x, SB.tsum 4 14 (fun t => TB.scale 4 (a t) (target_map 4 (S.table t) x)) = TB.zero 4) ->
     forall t, (t < 14)%nat -> a t = D.zero) /\
  (forall F : TB.cd 4 -> TB.cd 4, SB.linear 4 F ->
     (forall x y, F (TB.mul 4 x y) = TB.add 4 (TB.mul 4 (F x) y) (TB.mul 4 x (F y))) ->
     exists c : nat -> D.t, forall x,
       TB.scale 4 (H.h G2SpanTables.scalar) (F x) =
       SB.tsum 4 14 (fun t => TB.scale 4 (c t) (target_map 4 (S.table t) x))).
Proof.
  split; [| split].
  - intros t Ht x y.
    destruct t as [|[|[|[|[|[|[|[|[|[|[|[|[|[|t]]]]]]]]]]]]]];
      [exact (G.derivation_1 x y) |
       exact (G.derivation_2 x y) |
       exact (G.derivation_3 x y) |
       exact (G.derivation_4 x y) |
       exact (G.derivation_5 x y) |
       exact (G.derivation_6 x y) |
       exact (G.derivation_7 x y) |
       exact (G.derivation_8 x y) |
       exact (G.derivation_9 x y) |
       exact (G.derivation_10 x y) |
       exact (G.derivation_11 x y) |
       exact (G.derivation_12 x y) |
       exact (G.derivation_13 x y) |
       exact (G.derivation_14 x y) |
       exfalso; lia].
  - intros a R t Ht. exact (G.derivations_independent a R t Ht).
  - intros F L B. exists (S.span_coefficient F). intro x.
    apply (S.derivations_spanned F L). intros a b _ _. apply B.
Qed.

End G2DerivationBridge.

Module GaussianG2DerivationBridge := G2DerivationBridge GaussianIntegers.
