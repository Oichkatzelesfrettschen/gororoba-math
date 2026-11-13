(** Basis vectors and bilinear extension on the commutative-ring pair tower.

    RingTowerBasis extends RingTower of CdTowerRing.v, over the same
    signature CommutativeRing, with the standard basis of each level and the
    statements that reduce an identity of linear or bilinear maps to its
    values on basis vectors:

    - coord_basis: coordinate j of basis vector i is 1 when i = j and 0
      otherwise, for i, j below 2^k.
    - decompose: x is the sum over i below 2^k of coord(x, i) basis(i).
    - linear_ext: two maps that preserve sums and scalars and agree on the
      basis vectors agree everywhere.
    - bilinear_ext: the same for maps of two arguments.
    - multiplicative_by_basis: a linear map f with
      f(e_i e_j) = f(e_i) f(e_j) on all basis pairs preserves every product.
    - derivation_by_basis: a linear map that satisfies the Leibniz rule on
      all basis pairs satisfies it on every pair.
    - re_add, re_scale, re_one, re_conj: the real part is linear, is 1 on
      the unit and is fixed by conjugation.

    No step uses an order, cancellation, division or decidable equality on
    the coefficients. *)

From Stdlib Require Import Ring Lia PeanoNat.
Require Import CdTowerRing.

Module RingTowerBasis (D : CommutativeRing).
Module T := RingTower D.
Import T.
Add Ring basis_ring : D.ring_th.

Fixpoint basis (k : nat) : nat -> cd k :=
  match k as d return nat -> cd d with
  | O => fun _ => D.one
  | S j => fun i =>
      if Nat.ltb i (Nat.pow 2 j) then (basis j i, zero j) else (zero j, basis j (i - Nat.pow 2 j))
  end.

Lemma coord_basis k : forall i j, (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat ->
  coord k (basis k i) j = if Nat.eqb i j then D.one else D.zero.
Proof.
  induction k as [|n IH]; intros i j Hi Hj.
  - simpl in Hi, Hj. assert (i = O) as -> by lia. assert (j = O) as -> by lia. reflexivity.
  - cbn [basis coord Nat.pow] in *.
    destruct (Nat.ltb_spec i (Nat.pow 2 n)) as [Li|Li]; destruct (Nat.ltb_spec j (Nat.pow 2 n)) as [Lj|Lj];
      cbn [fst snd].
    + apply IH; assumption.
    + rewrite coord_zero. destruct (Nat.eqb_spec i j); [lia | reflexivity].
    + rewrite coord_zero. destruct (Nat.eqb_spec i j); [lia | reflexivity].
    + rewrite IH by lia.
      destruct (Nat.eqb_spec (i - Nat.pow 2 n) (j - Nat.pow 2 n)); destruct (Nat.eqb_spec i j);
        try reflexivity; lia.
Qed.

Fixpoint dsum (n : nat) (g : nat -> D.t) : D.t :=
  match n with O => D.zero | S m => D.add (dsum m g) (g m) end.

Fixpoint tsum (k n : nat) (g : nat -> cd k) : cd k :=
  match n with O => zero k | S m => add k (tsum k m g) (g m) end.

Lemma coord_tsum k n g i : coord k (tsum k n g) i = dsum n (fun m => coord k (g m) i).
Proof.
  induction n as [|m IH]; cbn [tsum dsum].
  - apply coord_zero.
  - rewrite coord_add, IH. reflexivity.
Qed.

Lemma dsum_ext n g h : (forall m, (m < n)%nat -> g m = h m) -> dsum n g = dsum n h.
Proof.
  induction n as [|m IH]; intro E; cbn [dsum]; [reflexivity |].
  rewrite IH by (intros; apply E; lia). rewrite E by lia. reflexivity.
Qed.

Lemma tsum_ext k n g h : (forall m, (m < n)%nat -> g m = h m) -> tsum k n g = tsum k n h.
Proof.
  induction n as [|m IH]; intro E; cbn [tsum]; [reflexivity |].
  rewrite IH by (intros; apply E; lia). rewrite E by lia. reflexivity.
Qed.

Lemma dsum_zero n : dsum n (fun _ => D.zero) = D.zero.
Proof. induction n as [|m IH]; cbn [dsum]; [reflexivity | rewrite IH; ring]. Qed.

Lemma dsum_delta n g j :
  dsum n (fun i => D.mul (g i) (if Nat.eqb i j then D.one else D.zero)) =
  if Nat.ltb j n then g j else D.zero.
Proof.
  induction n as [|m IH]; cbn [dsum].
  - reflexivity.
  - rewrite IH. destruct (Nat.ltb_spec j m) as [L|L]; destruct (Nat.ltb_spec j (S m)) as [L'|L']; try lia;
      destruct (Nat.eqb_spec m j) as [->|]; try lia; ring.
Qed.

Theorem decompose k x : x = tsum k (Nat.pow 2 k) (fun i => scale k (coord k x i) (basis k i)).
Proof.
  apply ext. intros j Hj. rewrite coord_tsum.
  rewrite (dsum_ext _ _ (fun i => D.mul (coord k x i) (if Nat.eqb i j then D.one else D.zero))).
  - rewrite dsum_delta. rewrite (proj2 (Nat.ltb_lt _ _) Hj). reflexivity.
  - intros m Hm. rewrite coord_scale, coord_basis by assumption. reflexivity.
Qed.

Lemma re_add k : forall x y, re k (add k x y) = D.add (re k x) (re k y).
Proof. induction k as [|n IH]; intros x y; cbn [re add fst]; [reflexivity | apply IH]. Qed.

Lemma re_scale k : forall r x, re k (scale k r x) = D.mul r (re k x).
Proof. induction k as [|n IH]; intros r x; cbn [re scale fst]; [reflexivity | apply IH]. Qed.

Lemma re_one k : re k (one k) = D.one.
Proof. induction k as [|n IH]; cbn [re one fst]; [reflexivity | apply IH]. Qed.

Lemma re_conj k : forall x, re k (conjugate k x) = re k x.
Proof. induction k as [|n IH]; intro x; cbn [re conjugate fst]; [reflexivity | apply IH]. Qed.

Definition linear k (h : cd k -> cd k) : Prop :=
  (forall x y, h (add k x y) = add k (h x) (h y)) /\ (forall r x, h (scale k r x) = scale k r (h x)).

Definition bilinear k (P : cd k -> cd k -> cd k) : Prop :=
  (forall y, linear k (fun x => P x y)) /\ (forall x, linear k (P x)).

Lemma scale_zero_coefficient k x : scale k D.zero x = zero k.
Proof. apply ext; intros ? _; rewrite coord_scale, coord_zero; ring. Qed.

Lemma linear_zero k h : linear k h -> h (zero k) = zero k.
Proof.
  intros [_ S]. rewrite <- (scale_zero_coefficient k (zero k)) at 1. rewrite S. apply scale_zero_coefficient.
Qed.

Lemma linear_tsum k h n g : linear k h -> h (tsum k n g) = tsum k n (fun m => h (g m)).
Proof.
  intro L. induction n as [|m IH]; cbn [tsum].
  - apply linear_zero, L.
  - destruct L as [A _]. rewrite A, IH. reflexivity.
Qed.

Theorem linear_ext k h g : linear k h -> linear k g ->
  (forall i, (i < Nat.pow 2 k)%nat -> h (basis k i) = g (basis k i)) -> forall x, h x = g x.
Proof.
  intros Lh Lg E x. rewrite (decompose k x) at 1 2.
  rewrite (linear_tsum k h _ _ Lh), (linear_tsum k g _ _ Lg).
  apply tsum_ext. intros m Hm.
  destruct Lh as [_ Sh], Lg as [_ Sg]. rewrite Sh, Sg, E by assumption. reflexivity.
Qed.

Theorem bilinear_ext k P Q : bilinear k P -> bilinear k Q ->
  (forall i j, (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat ->
     P (basis k i) (basis k j) = Q (basis k i) (basis k j)) ->
  forall x y, P x y = Q x y.
Proof.
  intros [Pl Pr] [Ql Qr] E x y.
  apply (linear_ext k (fun x => P x y) (fun x => Q x y) (Pl y) (Ql y)).
  intros i Hi. apply (linear_ext k (P (basis k i)) (Q (basis k i)) (Pr _) (Qr _)).
  intros j Hj. apply E; assumption.
Qed.

Lemma mul_bilinear k : bilinear k (mul k).
Proof.
  split; intro z; split; intros.
  - apply mul_add_l.
  - apply mul_scale_l.
  - apply mul_add_r.
  - apply mul_scale_r.
Qed.

(** A linear map that preserves the products of basis vectors preserves every product. *)
Theorem multiplicative_by_basis k f : linear k f ->
  (forall i j, (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat ->
     f (mul k (basis k i) (basis k j)) = mul k (f (basis k i)) (f (basis k j))) ->
  forall x y, f (mul k x y) = mul k (f x) (f y).
Proof.
  intros [Af Sf] E. apply (bilinear_ext k (fun x y => f (mul k x y)) (fun x y => mul k (f x) (f y))).
  - split; intro z; split; intros.
    + rewrite mul_add_l. apply Af.
    + rewrite mul_scale_l. apply Sf.
    + rewrite mul_add_r. apply Af.
    + rewrite mul_scale_r. apply Sf.
  - split; intro z; split; intros.
    + rewrite Af. apply mul_add_l.
    + rewrite Sf. apply mul_scale_l.
    + rewrite Af. apply mul_add_r.
    + rewrite Sf. apply mul_scale_r.
  - exact E.
Qed.

(** A linear map that satisfies the Leibniz rule on basis vectors is a derivation. *)
Theorem derivation_by_basis k f : linear k f ->
  (forall i j, (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat ->
     f (mul k (basis k i) (basis k j)) =
     add k (mul k (f (basis k i)) (basis k j)) (mul k (basis k i) (f (basis k j)))) ->
  forall x y, f (mul k x y) = add k (mul k (f x) y) (mul k x (f y)).
Proof.
  intros [Af Sf] E.
  apply (bilinear_ext k (fun x y => f (mul k x y)) (fun x y => add k (mul k (f x) y) (mul k x (f y)))).
  - split; intro z; split; intros.
    + rewrite mul_add_l. apply Af.
    + rewrite mul_scale_l. apply Sf.
    + rewrite mul_add_r. apply Af.
    + rewrite mul_scale_r. apply Sf.
  - split; intro z; split; intros.
    + rewrite Af, !mul_add_l. vec.
    + rewrite Sf, !mul_scale_l. vec.
    + rewrite Af, !mul_add_r. vec.
    + rewrite Sf, !mul_scale_r. vec.
  - exact E.
Qed.

End RingTowerBasis.
