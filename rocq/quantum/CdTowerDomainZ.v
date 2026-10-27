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
End ZBridge.
