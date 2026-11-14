(** The integer instance of CdTowerDomain.v is the tower of
    CdImaginarySumConference.v, operation by operation, so each theorem of
    the functor restates the theorem of CdAnnihilatorSymmetry.v in that
    file's vocabulary with no axiom: Print Assumptions on every statement
    below is empty. *)

From Stdlib Require Import ZArith.
Require Import CdTowerDomain.
Require CdImaginarySumConference.

Module ZBridge.
  Import CdImaginarySumConference.
  Lemma zero_eq : forall k, ZTower.zero k = zero k.
  Proof. induction k as [|j IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.
  Lemma one_eq : forall k, ZTower.one k = one k.
  Proof. induction k as [|j IH]; simpl; [reflexivity | rewrite IH, zero_eq; reflexivity]. Qed.
  Lemma add_eq : forall k x y, ZTower.add k x y = add k x y.
  Proof. induction k as [|j IH]; intros x y; simpl; [reflexivity | rewrite !IH; reflexivity]. Qed.
  Lemma scale_eq : forall k r x, ZTower.scale k r x = scale k r x.
  Proof. induction k as [|j IH]; intros r x; simpl; [reflexivity | rewrite !IH; reflexivity]. Qed.
  Lemma conjugate_eq : forall k x, ZTower.conjugate k x = conjugate k x.
  Proof. induction k as [|j IH]; intro x; simpl; [reflexivity | rewrite IH, scale_eq; reflexivity]. Qed.
  Lemma mul_eq : forall k x y, ZTower.mul k x y = mul k x y.
  Proof.
    induction k as [|j IH]; intros x y; simpl; [reflexivity |].
    rewrite !add_eq, !scale_eq, !conjugate_eq, !IH. reflexivity.
  Qed.
  Lemma re_eq : forall k x, ZTower.re k x = re k x.
  Proof. induction k as [|j IH]; intro x; simpl; [reflexivity | apply IH]. Qed.
  Lemma dot_eq : forall k x y, ZTower.dot k x y = dot k x y.
  Proof. induction k as [|j IH]; intros x y; simpl; [reflexivity | rewrite !IH; reflexivity]. Qed.

  Theorem kernel_equality k a z : mul k a z = zero k <-> mul k z a = zero k.
  Proof. rewrite <- !mul_eq, <- zero_eq. apply ZTower.kernel_equality. Qed.
  Theorem direct_finiteness k a b : mul k a b = one k -> mul k b a = one k.
  Proof. rewrite <- !mul_eq, <- one_eq. apply ZTower.direct_finiteness. Qed.
  Theorem flexible k x y : mul k (mul k x y) x = mul k x (mul k y x).
  Proof. rewrite <- !mul_eq. apply ZTower.flexible. Qed.
  Theorem purity_left k a z :
    mul k a z = zero k -> a <> zero k -> z <> zero k -> re k a = 0%Z /\ re k z = 0%Z.
  Proof. rewrite <- mul_eq, <- zero_eq, <- !re_eq. apply ZTower.purity_left. Qed.
  Theorem lemma_9_5 k (x y : cd (S k)) :
    mul (S k) x y = zero (S k) -> y <> zero (S k) ->
    dot (S k) x (one (S k)) = 0%Z /\ dot (S k) x (zero k, one k) = 0%Z.
  Proof. rewrite <- mul_eq, <- !zero_eq, <- !dot_eq, <- !one_eq. apply ZTower.lemma_9_5. Qed.
  (** The remaining theorems of the functor, restated the same way: every
      tower operation of the statement is rewritten to the instance's and
      the functor's theorem closes the goal by conversion. *)

  Ltac to_tower :=
    repeat first [rewrite <- mul_eq | rewrite <- conjugate_eq | rewrite <- add_eq | rewrite <- scale_eq
                 | rewrite <- dot_eq | rewrite <- re_eq | rewrite <- zero_eq | rewrite <- one_eq].

  Theorem conj_conj k x : conjugate k (conjugate k x) = x.
  Proof. to_tower. apply ZTower.conj_conj. Qed.
  Theorem conj_mul k x y : conjugate k (mul k x y) = mul k (conjugate k y) (conjugate k x).
  Proof. to_tower. apply ZTower.conj_mul. Qed.
  Theorem dot_conj k x y : dot k (conjugate k x) y = dot k x (conjugate k y).
  Proof. to_tower. apply ZTower.dot_conj. Qed.
  Theorem norm_mul k :
    (forall x, mul k x (conjugate k x) = scale k (dot k x x) (one k)) /\
    (forall x, mul k (conjugate k x) x = scale k (dot k x x) (one k)).
  Proof. split; intro x; to_tower; apply ZTower.norm_mul. Qed.
  Theorem adjoint k :
    (forall x y z, dot k (mul k x y) z = dot k y (mul k (conjugate k x) z)) /\
    (forall x y z, dot k (mul k x y) z = dot k x (mul k z (conjugate k y))).
  Proof. split; intros x y z; to_tower; apply ZTower.adjoint. Qed.
  Theorem re_commutator k x y : re k (mul k x y) = re k (mul k y x).
  Proof. to_tower. apply ZTower.re_commutator. Qed.
  Theorem re_associator k x y z : re k (mul k (mul k x y) z) = re k (mul k x (mul k y z)).
  Proof. to_tower. apply ZTower.re_associator. Qed.
  Theorem conj_mul_left k x y : mul k x (mul k (conjugate k x) y) = mul k (conjugate k x) (mul k x y).
  Proof. to_tower. apply ZTower.conj_mul_left. Qed.
  Theorem conj_mul_right k x y : mul k (mul k x y) (conjugate k y) = mul k (mul k x (conjugate k y)) y.
  Proof. to_tower. apply ZTower.conj_mul_right. Qed.
  Theorem lemma_9_2 k x y :
    (mul k x y = zero k <-> mul k (conjugate k x) y = zero k) /\
    (mul k x y = zero k <-> mul k x (conjugate k y) = zero k).
  Proof. to_tower. apply ZTower.lemma_9_2. Qed.
  Theorem purity_right k a z :
    mul k z a = zero k -> a <> zero k -> z <> zero k -> re k a = 0%Z /\ re k z = 0%Z.
  Proof. to_tower. apply ZTower.purity_right. Qed.
  Theorem annihilator_orthogonal k (x y : cd (S k)) :
    x <> zero (S k) -> mul (S k) x y = zero (S k) ->
    dot (S k) y (one (S k)) = 0%Z /\ dot (S k) y (zero k, one k) = 0%Z.
  Proof. to_tower. apply ZTower.annihilator_orthogonal. Qed.
  Theorem right_inverse_affine k a b :
    mul k a b = one k ->
    mul k a (add k (scale k (dot k a a) b) (scale k (-1)%Z (conjugate k a))) = zero k.
  Proof. to_tower. apply ZTower.right_inverse_affine. Qed.
End ZBridge.
