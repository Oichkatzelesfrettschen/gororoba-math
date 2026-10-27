(** The real instance of CdTowerDomain.v is the tower of CdTowerReal.v,
    operation by operation, so each theorem of the functor restates the
    theorem of CdAnnihilatorSymmetryReal.v in that file's vocabulary; the
    statements rest on the two Stdlib real-construction axioms alone. *)

From Stdlib Require Import Reals.
Require Import CdTowerDomain.
Require CdTowerReal.

Module RBridge.
  Import CdTowerReal.
  Lemma zero_eq : forall k, RTower.zero k = zero k.
  Proof. induction k as [|j IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.
  Lemma one_eq : forall k, RTower.one k = one k.
  Proof. induction k as [|j IH]; simpl; [reflexivity | rewrite IH, zero_eq; reflexivity]. Qed.
  Lemma add_eq : forall k x y, RTower.add k x y = add k x y.
  Proof. induction k as [|j IH]; intros x y; simpl; [reflexivity | rewrite !IH; reflexivity]. Qed.
  Lemma scale_eq : forall k r x, RTower.scale k r x = scale k r x.
  Proof. induction k as [|j IH]; intros r x; simpl; [reflexivity | rewrite !IH; reflexivity]. Qed.
  Lemma conjugate_eq : forall k x, RTower.conjugate k x = conjugate k x.
  Proof. induction k as [|j IH]; intro x; simpl; [reflexivity | rewrite IH, scale_eq; reflexivity]. Qed.
  Lemma mul_eq : forall k x y, RTower.mul k x y = mul k x y.
  Proof.
    induction k as [|j IH]; intros x y; simpl; [reflexivity |].
    rewrite !add_eq, !scale_eq, !conjugate_eq, !IH. reflexivity.
  Qed.
  Lemma re_eq : forall k x, RTower.re k x = re k x.
  Proof. induction k as [|j IH]; intro x; simpl; [reflexivity | apply IH]. Qed.
  Lemma dot_eq : forall k x y, RTower.dot k x y = dot k x y.
  Proof. induction k as [|j IH]; intros x y; simpl; [reflexivity | rewrite !IH; reflexivity]. Qed.

  Theorem kernel_equality k a z : mul k a z = zero k <-> mul k z a = zero k.
  Proof. rewrite <- !mul_eq, <- zero_eq. apply RTower.kernel_equality. Qed.
  Theorem direct_finiteness k a b : mul k a b = one k -> mul k b a = one k.
  Proof. rewrite <- !mul_eq, <- one_eq. apply RTower.direct_finiteness. Qed.
  Theorem flexible k x y : mul k (mul k x y) x = mul k x (mul k y x).
  Proof. rewrite <- !mul_eq. apply RTower.flexible. Qed.
  Theorem purity_left k a z :
    mul k a z = zero k -> a <> zero k -> z <> zero k -> re k a = 0%R /\ re k z = 0%R.
  Proof. rewrite <- mul_eq, <- zero_eq, <- !re_eq. apply RTower.purity_left. Qed.
  Theorem lemma_9_5 k (x y : cd (S k)) :
    mul (S k) x y = zero (S k) -> y <> zero (S k) ->
    dot (S k) x (one (S k)) = 0%R /\ dot (S k) x (zero k, one k) = 0%R.
  Proof. rewrite <- mul_eq, <- !zero_eq, <- !dot_eq, <- !one_eq. apply RTower.lemma_9_5. Qed.
End RBridge.

(** The field instance's tower is RTower's, and RTower's is CdTowerReal's, so
    the affine family restates right_inverse_form of
    CdAnnihilatorSymmetryReal.v. *)

Module RFieldBridge.
  Import CdTowerReal.
  Theorem right_inverse_form k a b :
    mul k a b = one k ->
    exists w, mul k a w = zero k /\ b = add k (scale k (/ dot k a a) (conjugate k a)) w.
  Proof.
    rewrite <- RBridge.mul_eq, <- RBridge.one_eq.
    intro H. destruct (RFieldTower.right_inverse_form k a b H) as [w [Hw E]].
    exists w. split.
    - rewrite <- RBridge.mul_eq, <- RBridge.zero_eq. exact Hw.
    - rewrite E, <- RBridge.add_eq, <- RBridge.scale_eq, <- RBridge.conjugate_eq, <- RBridge.dot_eq. reflexivity.
  Qed.
End RFieldBridge.
