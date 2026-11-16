(** * C-956: non-associativity at every order of the Cayley-Dickson tower from 8.

    Convention: cd_tower n of RecursiveCDTower.v is the real Cayley-Dickson
    algebra of dimension 2^n with the product tower_mul n; cd_tower 3 is the
    octonions and cd_tower 7 has dimension 128.  The embedding
    tower_embed n x = (x, 0) maps cd_tower n into cd_tower (S n).

    The module proves:
    - tower_embed preserves the product and is injective;
    - hence a triple of cd_tower n whose two products differ gives a triple of
      cd_tower (S n) whose two products differ;
    - the octonion triple (e1, e2, e4) of C909_OctonionNonAssociative, read
      in cd_tower 3, is such a triple, so for every order n >= 3 the tower
      has a triple a, b, c with (a b) c <> a (b c).

    The module states the existence of one violating triple at each order
    and no count of violating triples, so the size of the associator
    violation tensor at 128, 256, 512 or 1024 dimensions has no theorem. *)

From Stdlib Require Import Reals.
From OpenGororoba Require Import Prelude CayleyDicksonAlgebra Sedenion.
From OpenGororoba Require Import RecursiveCDTower CDConcreteTowerAdapter.
From OpenGororobaVerified Require Import C909_OctonionNonAssociative.

Definition tower_embed (n : nat) (x : cd_tower n) : cd_tower (S n) :=
  (x, tower_zero n).

Lemma tower_embed_mul : forall (n : nat) (x y : cd_tower n),
  tower_mul (S n) (tower_embed n x) (tower_embed n y) =
  tower_embed n (tower_mul n x y).
Proof.
  intros n x y. unfold tower_embed. simpl.
  rewrite tower_conj_zero, !tower_mul_zero_left.
  unfold tower_sub. rewrite tower_neg_zero.
  rewrite (tower_add_comm n (tower_mul n x y)), tower_add_zero.
  rewrite tower_add_zero.
  reflexivity.
Qed.

Lemma tower_embed_injective : forall (n : nat) (x y : cd_tower n),
  tower_embed n x = tower_embed n y -> x = y.
Proof.
  intros n x y H. unfold tower_embed in H.
  exact (f_equal fst H).
Qed.

Definition tower_nonassociative (n : nat) (a b c : cd_tower n) : Prop :=
  tower_mul n (tower_mul n a b) c <> tower_mul n a (tower_mul n b c).

Lemma tower_nonassociative_lifts : forall (n : nat) (a b c : cd_tower n),
  tower_nonassociative n a b c ->
  tower_nonassociative (S n) (tower_embed n a) (tower_embed n b) (tower_embed n c).
Proof.
  intros n a b c H Hlift. apply H.
  rewrite !tower_embed_mul in Hlift.
  exact (tower_embed_injective n _ _ Hlift).
Qed.

Lemma tower_octonion_triple_nonassociative :
  tower_nonassociative 3 (octonion_tower oe1) (octonion_tower oe2)
                         (octonion_tower oe4).
Proof.
  unfold tower_nonassociative. intro H.
  apply C909_octonion_non_associative.
  apply (f_equal tower_octonion) in H.
  rewrite !tower_octonion_mul in H.
  rewrite !tower_octonion_round_trip in H.
  exact H.
Qed.

Theorem tower_nonassociative_from_order_3 : forall n : nat,
  (3 <= n)%nat ->
  exists a b c : cd_tower n, tower_nonassociative n a b c.
Proof.
  intros n Hn. induction Hn as [| n Hn IH].
  - exists (octonion_tower oe1), (octonion_tower oe2), (octonion_tower oe4).
    exact tower_octonion_triple_nonassociative.
  - destruct IH as [a [b [c H]]].
    exists (tower_embed n a), (tower_embed n b), (tower_embed n c).
    exact (tower_nonassociative_lifts n a b c H).
Qed.

(** Dimension 128 is order 7. *)
Corollary tower_nonassociative_dim_128 :
  exists a b c : cd_tower 7, tower_nonassociative 7 a b c.
Proof. apply tower_nonassociative_from_order_3. repeat constructor. Qed.
