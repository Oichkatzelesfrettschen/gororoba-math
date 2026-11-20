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
    - hT, each T t satisfies the Leibniz rule on all of level 4: the Leibniz rule of its table on the 256 pairs
      of source basis units, decided by evaluation, carried to D by derivation_transport of
      CdTowerRingBaseChange.v, the instance phi := h, k := 4, F := the map of images_(t+1) of
      Tower.baseChange_leibniz of lean/GororobaMath/CayleyDickson/BaseChange.lean;
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


(** S and G instantiate BaseChange GaussianIntegers D H separately. Their operations agree by unfolding at a
    variable level; stated at level 4, the unifier and the kernel evaluate the 2^4 sums (a check of the level-4
    form ran past 240 s, Rocq 9.3.0), so the equalities below hold at every level and are specialized by
    rewriting. *)

Lemma scale_same k c x : TB.scale k c x = G.BC.TB.scale k c x.
Proof. reflexivity. Qed.

Lemma zero_same k : TB.zero k = G.BC.TB.zero k.
Proof. reflexivity. Qed.

Lemma tsum_same k n g : SB.tsum k n g = G.BC.SB.tsum k n g.
Proof. reflexivity. Qed.

Lemma target_map_same k (f : nat -> TA.cd k) x : target_map k f x = G.BC.target_map k f x.
Proof. reflexivity. Qed.

Lemma table_images t m : S.table t m = G.images t m.
Proof. reflexivity. Qed.

Lemma target_map_table t x : target_map 4 (S.table t) x = G.BC.target_map 4 (G.images t) x.
Proof.
  rewrite target_map_same. unfold G.BC.target_map. apply G.BC.SB.tsum_ext. intros m _.
  rewrite table_images. reflexivity.
Qed.

Ltac basis_pairs :=
  intros i j Hi Hj; change (Nat.pow 2 4) with 16%nat in Hi, Hj;
  do 16 (destruct i as [|i];
    [ do 16 (destruct j as [|j]; [vm_compute; reflexivity |]); exfalso; lia |]);
  exfalso; lia.

(** The Leibniz rule of each table on the 256 pairs of source basis units, decided by evaluation in the base change
    of S, so that the transport below stays inside one instance of BaseChange. *)
Lemma source_leibniz t : (t < 14)%nat -> forall i j, (i < Nat.pow 2 4)%nat -> (j < Nat.pow 2 4)%nat ->
  source_map 4 (S.table t) (TA.mul 4 (SA.basis 4 i) (SA.basis 4 j)) =
  TA.add 4 (TA.mul 4 (source_map 4 (S.table t) (SA.basis 4 i)) (SA.basis 4 j))
           (TA.mul 4 (SA.basis 4 i) (source_map 4 (S.table t) (SA.basis 4 j))).
Proof.
  intro Ht. destruct t as [|[|[|[|[|[|[|[|[|[|[|[|[|[|t]]]]]]]]]]]]]]; [basis_pairs | basis_pairs | basis_pairs | basis_pairs | basis_pairs | basis_pairs | basis_pairs | basis_pairs | basis_pairs | basis_pairs | basis_pairs | basis_pairs | basis_pairs | basis_pairs | exfalso; lia].
Qed.

Lemma clause_derivations : forall t, (t < 14)%nat -> forall x y,
     target_map 4 (S.table t) (TB.mul 4 x y) =
     TB.add 4 (TB.mul 4 (target_map 4 (S.table t) x) y) (TB.mul 4 x (target_map 4 (S.table t) y)).
Proof. intros t Ht. exact (derivation_transport 4 (S.table t) (source_leibniz t Ht)). Qed.

Lemma clause_independent : forall a : nat -> D.t,
     (forall x, SB.tsum 4 14 (fun t => TB.scale 4 (a t) (target_map 4 (S.table t) x)) = TB.zero 4) ->
     forall t, (t < 14)%nat -> a t = D.zero.
Proof.
  intros a R t Ht. apply (G.derivations_independent a); [| exact Ht].
  intro x. transitivity (SB.tsum 4 14 (fun t => TB.scale 4 (a t) (target_map 4 (S.table t) x))).
  - symmetry. rewrite tsum_same. apply G.BC.SB.tsum_ext. intros n _.
    rewrite target_map_table, scale_same. reflexivity.
  - rewrite (R x). apply zero_same.
Qed.

Lemma clause_spanned : forall F : TB.cd 4 -> TB.cd 4, SB.linear 4 F ->
     (forall x y, F (TB.mul 4 x y) = TB.add 4 (TB.mul 4 (F x) y) (TB.mul 4 x (F y))) ->
     exists c : nat -> D.t, forall x,
       TB.scale 4 (H.h G2SpanTables.scalar) (F x) =
       SB.tsum 4 14 (fun t => TB.scale 4 (c t) (target_map 4 (S.table t) x)).
Proof.
  intros F L B. exists (S.span_coefficient F). intro x.
  apply (S.derivations_spanned F L). intros a b _ _. apply B.
Qed.

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
Proof. exact (conj clause_derivations (conj clause_independent clause_spanned)). Qed.

End G2DerivationBridge.

Module GaussianG2DerivationBridge := G2DerivationBridge GaussianIntegers.
