(** Base change of the commutative-ring pair tower along a ring homomorphism.

    RingHom states a map h of commutative rings that preserves 0, 1, sums,
    products and negatives. BaseChange applies h to every coordinate
    (tmap) and proves that tmap preserves zero, one, sums, scalars (through
    h), conjugates, products, real parts, coordinates and basis vectors.

    source_map k images and target_map k images are the linear maps of
    level k whose values on the basis vectors are images(i) over the source
    ring and tmap(images(i)) over the target ring; target_map_tmap states
    that tmap carries the first onto the second. Two transport theorems
    turn a finite check over the source ring into a statement about every
    element over the target ring:

    - derivation_transport: the Leibniz rule on all basis pairs over the
      source ring gives the Leibniz rule for target_map on all pairs.
    - scaled_multiplicative_transport: f(e_i) f(e_j) = c f(e_i e_j) on all
      basis pairs over the source ring gives
      target_map(x) target_map(y) = h(c) target_map(x y) on all pairs.

    IntegerRing is Z as a CommutativeRing and IntegerHom is the unique
    homomorphism from Z to a commutative ring (Stdlib's gen_phiZ with
    gen_phiZ_morph), so a computation over the integers transfers to every
    commutative ring. *)

From Stdlib Require Import Ring Lia PeanoNat ZArith InitialRing Setoid.
Require Import CdTowerRing CdTowerRingBasis.

Module Type RingHom (A B : CommutativeRing).
  Parameter h : A.t -> B.t.
  Axiom h_zero : h A.zero = B.zero.
  Axiom h_one : h A.one = B.one.
  Axiom h_add : forall x y, h (A.add x y) = B.add (h x) (h y).
  Axiom h_mul : forall x y, h (A.mul x y) = B.mul (h x) (h y).
  Axiom h_opp : forall x, h (A.opp x) = B.opp (h x).
End RingHom.

Module BaseChange (A B : CommutativeRing) (H : RingHom A B).
Module SA := RingTowerBasis A.
Module SB := RingTowerBasis B.
Module TA := SA.T.
Module TB := SB.T.
Add Ring base_change_source : A.ring_th.
Add Ring base_change_target : B.ring_th.

Ltac target_vector :=
  apply TB.ext; intros ? _;
  repeat (rewrite TB.coord_add || rewrite TB.coord_scale || rewrite TB.coord_zero); ring.

Fixpoint tmap (k : nat) : TA.cd k -> TB.cd k :=
  match k as d return TA.cd d -> TB.cd d with
  | O => H.h
  | S j => fun x => (tmap j (fst x), tmap j (snd x))
  end.

Lemma h_neg_one : H.h TA.neg_one = TB.neg_one.
Proof. unfold TA.neg_one, TB.neg_one. rewrite H.h_opp, H.h_one. reflexivity. Qed.

Lemma tmap_zero k : tmap k (TA.zero k) = TB.zero k.
Proof. induction k as [|j IH]; cbn [tmap TA.zero TB.zero fst snd]; [apply H.h_zero | rewrite IH; reflexivity]. Qed.

Lemma tmap_one k : tmap k (TA.one k) = TB.one k.
Proof.
  induction k as [|j IH]; cbn [tmap TA.one TB.one fst snd]; [apply H.h_one | rewrite IH, tmap_zero; reflexivity].
Qed.

Lemma tmap_add k : forall x y, tmap k (TA.add k x y) = TB.add k (tmap k x) (tmap k y).
Proof.
  induction k as [|j IH]; intros x y; cbn [tmap TA.add TB.add fst snd]; [apply H.h_add | rewrite !IH; reflexivity].
Qed.

Lemma tmap_scale k : forall r x, tmap k (TA.scale k r x) = TB.scale k (H.h r) (tmap k x).
Proof.
  induction k as [|j IH]; intros r x; cbn [tmap TA.scale TB.scale fst snd]; [apply H.h_mul | rewrite !IH; reflexivity].
Qed.

Lemma tmap_conj k : forall x, tmap k (TA.conjugate k x) = TB.conjugate k (tmap k x).
Proof.
  induction k as [|j IH]; intro x; cbn [tmap TA.conjugate TB.conjugate fst snd]; [reflexivity |].
  rewrite IH, tmap_scale, h_neg_one. reflexivity.
Qed.

Lemma tmap_mul k : forall x y, tmap k (TA.mul k x y) = TB.mul k (tmap k x) (tmap k y).
Proof.
  induction k as [|j IH]; intros x y; cbn [tmap TA.mul TB.mul fst snd]; [apply H.h_mul |].
  rewrite !tmap_add, !tmap_scale, !IH, !tmap_conj, h_neg_one. reflexivity.
Qed.

Lemma tmap_re k : forall x, H.h (TA.re k x) = TB.re k (tmap k x).
Proof. induction k as [|j IH]; intro x; cbn [tmap TA.re TB.re fst snd]; [reflexivity | apply IH]. Qed.

Lemma tmap_coord k : forall x i, H.h (TA.coord k x i) = TB.coord k (tmap k x) i.
Proof.
  induction k as [|j IH]; intros x i; cbn [tmap TA.coord TB.coord fst snd]; [reflexivity |].
  destruct (Nat.ltb i (Nat.pow 2 j)); apply IH.
Qed.

Lemma tmap_basis k : forall i, tmap k (SA.basis k i) = SB.basis k i.
Proof.
  induction k as [|j IH]; intro i; cbn [tmap SA.basis SB.basis]; [apply H.h_one |].
  destruct (Nat.ltb i (Nat.pow 2 j)); cbn [tmap fst snd]; rewrite IH, tmap_zero; reflexivity.
Qed.

Lemma tmap_tsum k n g : tmap k (SA.tsum k n g) = SB.tsum k n (fun m => tmap k (g m)).
Proof.
  induction n as [|m IH]; cbn [SA.tsum SB.tsum]; [apply tmap_zero | rewrite tmap_add, IH; reflexivity].
Qed.

(** The linear map of level k with prescribed images of the basis vectors. *)
Definition source_map k (images : nat -> TA.cd k) (x : TA.cd k) : TA.cd k :=
  SA.tsum k (Nat.pow 2 k) (fun i => TA.scale k (TA.coord k x i) (images i)).

Definition target_map k (images : nat -> TA.cd k) (x : TB.cd k) : TB.cd k :=
  SB.tsum k (Nat.pow 2 k) (fun i => TB.scale k (TB.coord k x i) (tmap k (images i))).

Lemma target_map_tmap k images x : target_map k images (tmap k x) = tmap k (source_map k images x).
Proof.
  unfold target_map, source_map. rewrite tmap_tsum. apply SB.tsum_ext. intros m _.
  rewrite tmap_scale, tmap_coord. reflexivity.
Qed.

Lemma target_map_linear k images : SB.linear k (target_map k images).
Proof.
  split; intros; unfold target_map; apply TB.ext; intros j _; rewrite ?TB.coord_add, ?TB.coord_scale, !SB.coord_tsum.
  - induction (Nat.pow 2 k) as [|m IH]; cbn [SB.dsum]; [ring |].
    rewrite IH, !TB.coord_scale, TB.coord_add. ring.
  - induction (Nat.pow 2 k) as [|m IH]; cbn [SB.dsum]; [ring |].
    rewrite IH, !TB.coord_scale. ring.
Qed.

Lemma source_map_basis k images i : (i < Nat.pow 2 k)%nat ->
  source_map k images (SA.basis k i) =
  SA.tsum k (Nat.pow 2 k) (fun m => TA.scale k (if Nat.eqb i m then A.one else A.zero) (images m)).
Proof.
  intro Hi. unfold source_map. apply SA.tsum_ext. intros m Hm. rewrite SA.coord_basis by assumption. reflexivity.
Qed.

(** Leibniz rule: checked on the basis vectors of the source ring, it holds for every pair of elements of
    the target ring. *)
Theorem derivation_transport k images :
  (forall i j, (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat ->
     source_map k images (TA.mul k (SA.basis k i) (SA.basis k j)) =
     TA.add k (TA.mul k (source_map k images (SA.basis k i)) (SA.basis k j))
              (TA.mul k (SA.basis k i) (source_map k images (SA.basis k j)))) ->
  forall x y, target_map k images (TB.mul k x y) =
              TB.add k (TB.mul k (target_map k images x) y) (TB.mul k x (target_map k images y)).
Proof.
  intro E. apply (SB.derivation_by_basis k _ (target_map_linear k images)). intros i j Hi Hj.
  rewrite <- !tmap_basis, <- tmap_mul, !target_map_tmap, <- !tmap_mul, <- tmap_add.
  f_equal. apply E; assumption.
Qed.

(** Products up to a scalar factor: mul (f x) (f y) = c f (x y), checked on the basis vectors of the source
    ring, holds for every pair of elements of the target ring. *)
Theorem scaled_multiplicative_transport k images c :
  (forall i j, (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat ->
     TA.mul k (source_map k images (SA.basis k i)) (source_map k images (SA.basis k j)) =
     TA.scale k c (source_map k images (TA.mul k (SA.basis k i) (SA.basis k j)))) ->
  forall x y, TB.mul k (target_map k images x) (target_map k images y) =
              TB.scale k (H.h c) (target_map k images (TB.mul k x y)).
Proof.
  intro E. destruct (target_map_linear k images) as [Af Sf].
  apply (SB.bilinear_ext k (fun x y => TB.mul k (target_map k images x) (target_map k images y))
           (fun x y => TB.scale k (H.h c) (target_map k images (TB.mul k x y)))).
  - split; intro z; split; intros.
    + rewrite Af. apply TB.mul_add_l.
    + rewrite Sf. apply TB.mul_scale_l.
    + rewrite Af. apply TB.mul_add_r.
    + rewrite Sf. apply TB.mul_scale_r.
  - split; intro z; split; intros.
    + rewrite TB.mul_add_l, Af. target_vector.
    + rewrite TB.mul_scale_l, Sf. target_vector.
    + rewrite TB.mul_add_r, Af. target_vector.
    + rewrite TB.mul_scale_r, Sf. target_vector.
  - intros i j Hi Hj.
    rewrite <- !tmap_basis, <- tmap_mul, !target_map_tmap, <- tmap_mul, <- tmap_scale.
    f_equal. apply E; assumption.
Qed.

End BaseChange.

(** The integers, and the unique ring homomorphism from them to a commutative ring. *)

Module IntegerRing <: CommutativeRing.
  Definition t := Z.
  Definition zero := 0%Z.
  Definition one := 1%Z.
  Definition add := Z.add.
  Definition mul := Z.mul.
  Definition sub := Z.sub.
  Definition opp := Z.opp.
  Lemma ring_th : ring_theory zero one add mul sub opp (@eq t). Proof. exact Zth. Qed.
End IntegerRing.

Module IntegerHom (D : CommutativeRing) <: RingHom IntegerRing D.
  Definition h : Z -> D.t := gen_phiZ D.zero D.one D.add D.mul D.opp.
  Lemma h_morph :
    ring_morph D.zero D.one D.add D.mul D.sub D.opp (@eq D.t) 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb h.
  Proof.
    apply gen_phiZ_morph; [exact (Eqsth D.t) | exact (Eq_ext D.add D.mul D.opp) | exact D.ring_th].
  Qed.
  Lemma h_zero : h IntegerRing.zero = D.zero. Proof. exact (morph0 h_morph). Qed.
  Lemma h_one : h IntegerRing.one = D.one. Proof. exact (morph1 h_morph). Qed.
  Lemma h_add : forall x y, h (IntegerRing.add x y) = D.add (h x) (h y). Proof. exact (morph_add h_morph). Qed.
  Lemma h_mul : forall x y, h (IntegerRing.mul x y) = D.mul (h x) (h y). Proof. exact (morph_mul h_morph). Qed.
  Lemma h_opp : forall x, h (IntegerRing.opp x) = D.opp (h x). Proof. exact (morph_opp h_morph). Qed.
End IntegerHom.
