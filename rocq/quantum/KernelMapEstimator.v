(** The nullity estimator over a field of characteristic zero: the Rocq
    bridge of the headline theorems KernelMap.nHat_sub_nullity and
    KernelMap.nHat_eq_card_div_two_of_negBins_eq_empty of
    lean/GororobaMath/KernelMap/Estimator.lean.

    Convention: the Lean module reads a block of bins B (a Finset), an
    observed contrast c from the bins to a field K of characteristic zero,
    and a predicate pos that marks the bins of ideal contrast +1. The
    definitions below carry the Lean names and formulas:

      vHat      = (sum over B of c y * (1 if pos y else -1)) / |B|
      nHat      = (sum over B of c y) / 2 / vHat
      nullity   = (|B+| - |B-|) / 2
      vBarPos   = (sum over B+ of c y) / |B+|
      vBarNeg   = (sum over B- of -c y) / |B-|

    with B+ = posBins B pos and B- = negBins B pos the bins that satisfy
    and falsify pos. The Rocq block is a list, so the sums are
    right-associated folds and the cardinalities are lengths; a Lean
    Finset is a list without repeated entries (Finset.toList), and each
    statement here holds for every list, so no hypothesis of no repetition
    enters. The predicate is a bool function where Lean takes a decidable
    Prop. A natural number n acts on the field as n copies of one added to
    zero (ofnat), which is Lean's Nat.cast. The field is the signature
    CharZeroField: a field_theory over Leibniz equality with
    Nat.iter n (add one) zero = zero only for n = 0, which is Lean's
    Field and CharZero. Lean divides by zero to get zero where field_theory
    leaves the inverse of zero unspecified; neither statement below uses
    the value of a quotient by zero, since an empty class contributes an
    empty sum, and a block with no bin reads vHat = 0.

    The functor Estimator restates the two theorems at a field F:

    - nHat_sub_nullity is KernelMap.nHat_sub_nullity: for vHat <> 0,
      nHat - nullity = |B+| |B-| / |B| * (vBarPos - vBarNeg) / vHat,
      associated as in Lean, ((|B+| |B-|) / |B| * (vBarPos - vBarNeg)) / vHat.
    - nHat_eq_card_div_two_of_negBins_eq_nil is
      KernelMap.nHat_eq_card_div_two_of_negBins_eq_empty: for vHat <> 0 and
      negBins B pos = nil, nHat = |B| / 2.

    The statements are not narrower than the Lean ones: the field is any
    field of characteristic zero with Leibniz equality. The module Defs
    holds the definitions over the operations alone, so that a computation
    can instantiate them with the rationals (ci/compare_estimator_rocq.sh
    compares them with the Lean definitions); RealEstimator instantiates
    the functor at the real numbers of the standard library. *)

From Stdlib Require Import Field List Lia Reals.
Import ListNotations.

Module Type FieldOps.
  Parameter t : Type.
  Parameter zero one : t.
  Parameter add mul sub : t -> t -> t.
  Parameter opp inv : t -> t.
  Parameter div : t -> t -> t.
End FieldOps.

Module Type CharZeroField.
  Include FieldOps.
  Axiom field_th : field_theory zero one add mul sub opp div inv (@eq t).
  Axiom char_zero : forall n : nat, Nat.iter n (add one) zero = zero -> n = 0%nat.
End CharZeroField.

Module Defs (F : FieldOps).

Definition two : F.t := F.add F.one F.one.
Definition ofnat (n : nat) : F.t := Nat.iter n (F.add F.one) F.zero.
Definition sum {A : Type} (f : A -> F.t) (l : list A) : F.t :=
  fold_right (fun y acc => F.add (f y) acc) F.zero l.

Section Block.
Context {A : Type} (B : list A) (c : A -> F.t) (pos : A -> bool).

Definition posBins : list A := filter pos B.
Definition negBins : list A := filter (fun y => negb (pos y)) B.

Definition vHat : F.t :=
  F.div (sum (fun y => F.mul (c y) (if pos y then F.one else F.opp F.one)) B) (ofnat (length B)).
Definition nHat : F.t := F.div (F.div (sum c B) two) vHat.
Definition nullity : F.t :=
  F.div (F.sub (ofnat (length posBins)) (ofnat (length negBins))) two.
Definition vBarPos : F.t := F.div (sum c posBins) (ofnat (length posBins)).
Definition vBarNeg : F.t :=
  F.div (sum (fun y => F.opp (c y)) negBins) (ofnat (length negBins)).

End Block.

End Defs.

Module Estimator (F : CharZeroField).
Module D := Defs F.
Import D.
Add Field estimator_field : F.field_th.

Lemma ofnat_succ n : ofnat (S n) = F.add F.one (ofnat n).
Proof. reflexivity. Qed.

Lemma ofnat_zero : ofnat 0 = F.zero.
Proof. reflexivity. Qed.

Lemma ofnat_add n m : ofnat (n + m) = F.add (ofnat n) (ofnat m).
Proof.
  induction n as [|n IH].
  - rewrite Nat.add_0_l, ofnat_zero. ring.
  - rewrite Nat.add_succ_l, !ofnat_succ, IH. ring.
Qed.

Lemma ofnat_nonzero n : n <> 0%nat -> ofnat n <> F.zero.
Proof. intros H E. exact (H (F.char_zero n E)). Qed.

Lemma two_nonzero : two <> F.zero.
Proof.
  intro E. assert (H : ofnat 2 = F.zero).
  { transitivity two; [|exact E]. unfold ofnat, two. simpl. ring. }
  exact (ofnat_nonzero 2 ltac:(discriminate) H).
Qed.

Lemma div_zero_l (x : F.t) : F.div F.zero x = F.zero.
Proof. rewrite (Fdiv_def F.field_th). ring. Qed.

Lemma mul_div_ofnat (x : F.t) n : (n = 0%nat -> x = F.zero) -> F.mul (ofnat n) (F.div x (ofnat n)) = x.
Proof.
  intro H. destruct n as [|m].
  - rewrite (H eq_refl), ofnat_zero. ring.
  - field. exact (ofnat_nonzero (S m) ltac:(discriminate)).
Qed.

Section Block.
Context {A : Type} (B : list A) (c : A -> F.t) (pos : A -> bool).

Lemma length_split :
  (length (posBins B pos) + length (negBins B pos) = length B)%nat.
Proof.
  unfold posBins, negBins. induction B as [|y l IH]; simpl.
  - reflexivity.
  - destruct (pos y); simpl; lia.
Qed.

Lemma sum_split : sum c B = F.add (sum c (posBins B pos)) (sum c (negBins B pos)).
Proof.
  unfold sum, posBins, negBins. induction B as [|y l IH]; simpl.
  - ring.
  - destruct (pos y); simpl; rewrite IH; ring.
Qed.

Lemma signed_sum_split :
  sum (fun y => F.mul (c y) (if pos y then F.one else F.opp F.one)) B =
  F.sub (sum c (posBins B pos)) (sum c (negBins B pos)).
Proof.
  unfold sum, posBins, negBins. induction B as [|y l IH]; simpl.
  - ring.
  - destruct (pos y); simpl; rewrite IH; ring.
Qed.

Lemma sum_opp (l : list A) : sum (fun y => F.opp (c y)) l = F.opp (sum c l).
Proof.
  unfold sum. induction l as [|y l IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma sum_nil_of_length (l : list A) : length l = 0%nat -> sum c l = F.zero.
Proof. destruct l as [|y l]; simpl; [intros _; reflexivity | discriminate]. Qed.

Lemma card_mul_vBarPos :
  F.mul (ofnat (length (posBins B pos))) (vBarPos B c pos) = sum c (posBins B pos).
Proof. unfold vBarPos. apply mul_div_ofnat. apply sum_nil_of_length. Qed.

Lemma card_mul_vBarNeg :
  F.mul (ofnat (length (negBins B pos))) (vBarNeg B c pos) = F.opp (sum c (negBins B pos)).
Proof.
  unfold vBarNeg. rewrite sum_opp. apply mul_div_ofnat. intro H.
  rewrite (sum_nil_of_length _ H). ring.
Qed.

Lemma card_eq : ofnat (length B) = F.add (ofnat (length (posBins B pos))) (ofnat (length (negBins B pos))).
Proof. rewrite <- ofnat_add, length_split. reflexivity. Qed.

Lemma vHat_eq :
  vHat B c pos =
  F.div (F.add (F.mul (ofnat (length (posBins B pos))) (vBarPos B c pos))
               (F.mul (ofnat (length (negBins B pos))) (vBarNeg B c pos)))
        (F.add (ofnat (length (posBins B pos))) (ofnat (length (negBins B pos)))).
Proof.
  unfold vHat. rewrite signed_sum_split, card_eq, card_mul_vBarPos, card_mul_vBarNeg.
  f_equal. ring.
Qed.

Lemma vHat_nil : length B = 0%nat -> vHat B c pos = F.zero.
Proof.
  intro H. unfold vHat. destruct B as [|y l]; [|discriminate].
  cbn [length]. unfold sum. cbn [fold_right]. rewrite ofnat_zero. apply div_zero_l.
Qed.

(** The bias identity on the five numbers it depends on. *)
Lemma nHat_sub_nullity_scalar (a b u v : F.t) :
  F.add a b <> F.zero -> F.add (F.mul a u) (F.mul b v) <> F.zero ->
  F.sub (F.div (F.div (F.sub (F.mul a u) (F.mul b v)) two)
               (F.div (F.add (F.mul a u) (F.mul b v)) (F.add a b)))
        (F.div (F.sub a b) two) =
  F.div (F.mul (F.div (F.mul a b) (F.add a b)) (F.sub u v))
        (F.div (F.add (F.mul a u) (F.mul b v)) (F.add a b)).
Proof.
  intros hn hV. pose proof two_nonzero as h2. unfold two in *.
  field; auto.
Qed.

Theorem nHat_sub_nullity (hV : vHat B c pos <> F.zero) :
  F.sub (nHat B c pos) (nullity B pos) =
  F.div (F.mul (F.div (F.mul (ofnat (length (posBins B pos))) (ofnat (length (negBins B pos))))
                      (ofnat (length B)))
               (F.sub (vBarPos B c pos) (vBarNeg B c pos)))
        (vHat B c pos).
Proof.
  set (p := ofnat (length (posBins B pos))).
  set (q := ofnat (length (negBins B pos))).
  set (u := vBarPos B c pos). set (v := vBarNeg B c pos).
  assert (Hcard : ofnat (length B) = F.add p q) by apply card_eq.
  assert (Hn : F.add p q <> F.zero).
  { rewrite <- Hcard. intro E. apply hV. apply vHat_nil. exact (F.char_zero _ E). }
  assert (HV : vHat B c pos = F.div (F.add (F.mul p u) (F.mul q v)) (F.add p q))
    by apply vHat_eq.
  assert (HS : F.add (F.mul p u) (F.mul q v) <> F.zero).
  { intro E. apply hV. rewrite HV, E. field. exact Hn. }
  assert (Hsum : sum c B = F.sub (F.mul p u) (F.mul q v)).
  { unfold p, q, u, v. rewrite sum_split, card_mul_vBarPos, card_mul_vBarNeg. ring. }
  unfold nHat, nullity. rewrite Hsum, HV, Hcard.
  exact (nHat_sub_nullity_scalar p q u v Hn HS).
Qed.

Theorem nHat_eq_nullity_of_negBins_eq_nil (hV : vHat B c pos <> F.zero)
  (hneg : negBins B pos = []) : nHat B c pos = nullity B pos.
Proof.
  pose proof (nHat_sub_nullity hV) as H. rewrite hneg in H.
  replace (ofnat (length ([] : list A))) with F.zero in H by reflexivity.
  rewrite !(Fdiv_def F.field_th) in H.
  transitivity (F.add (F.sub (nHat B c pos) (nullity B pos)) (nullity B pos)); [ring|].
  rewrite H. ring.
Qed.

Theorem nHat_eq_card_div_two_of_negBins_eq_nil (hV : vHat B c pos <> F.zero)
  (hneg : negBins B pos = []) : nHat B c pos = F.div (ofnat (length B)) two.
Proof.
  rewrite (nHat_eq_nullity_of_negBins_eq_nil hV hneg). unfold nullity.
  rewrite card_eq, hneg. cbn [length]. rewrite ofnat_zero. field. exact two_nonzero.
Qed.

End Block.

End Estimator.

Module RealField <: CharZeroField.
  Definition t : Type := R.
  Definition zero : t := 0%R.
  Definition one : t := 1%R.
  Definition add : t -> t -> t := Rplus.
  Definition mul : t -> t -> t := Rmult.
  Definition sub : t -> t -> t := Rminus.
  Definition opp : t -> t := Ropp.
  Definition inv : t -> t := Rinv.
  Definition div : t -> t -> t := Rdiv.
  Lemma field_th : field_theory zero one add mul sub opp div inv (@eq t).
  Proof. exact Rfield. Qed.
  Lemma iter_INR n : Nat.iter n (add one) zero = INR n.
  Proof.
    induction n as [|n IH]; [reflexivity|].
    change (add one (Nat.iter n (add one) zero) = INR (S n)). rewrite IH, S_INR.
    unfold add, one. apply Rplus_comm.
  Qed.
  Lemma char_zero : forall n : nat, Nat.iter n (add one) zero = zero -> n = 0%nat.
  Proof.
    intros n H. rewrite iter_INR in H. destruct n as [|m]; [reflexivity|].
    exfalso. exact (not_0_INR (S m) ltac:(discriminate) H).
  Qed.
End RealField.

Module RealEstimator := Estimator RealField.
