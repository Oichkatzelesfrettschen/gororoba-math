(** Kernel certificates for left multiplication on the commutative-ring tower.

    For an element y of level k over a source ring A, a certificate of the kernel of z -> y z is
    - n vectors v_0 .. v_(n-1) with y v_j = 0,
    - n coordinate functionals f_0 .. f_(n-1) with f_j(v_l) = d for j = l and 0 otherwise,
    - a table `back` of 2^k images and a scalar d with
        d z = back(y z) + sum_j f_j(z) v_j
      on the basis vectors of the source ring.
    The three finite checks over A give, over every commutative ring B that receives a homomorphism h from A:
    the v_j are annihilated by y, every z with y z = 0 satisfies h(d) z = sum_j f_j(z) v_j, and a combination
    sum_j a_j v_j determines h(d) a_j. Where h(d) is invertible, the kernel of z -> y z is the free module on
    v_0 .. v_(n-1).

    Convention: the product is `mul` of CdTowerRing.v; a functional is a vector u acting by the coordinate
    pairing u(x) = sum_i coord_i(u) coord_i(x), in the coordinate basis of CdTowerRingBasis.v. *)

From Stdlib Require Import Ring Lia PeanoNat.
Require Import CdTowerRing CdTowerRingBasis CdTowerRingBaseChange.

Module KernelCertificate (A B : CommutativeRing) (H : RingHom A B).
Module BC := BaseChange A B H.
Import BC.

Add Ring kernel_certificate_source : A.ring_th.
Add Ring kernel_certificate_target : B.ring_th.

Definition source_pair k (u x : TA.cd k) : A.t :=
  SA.dsum (Nat.pow 2 k) (fun i => A.mul (TA.coord k u i) (TA.coord k x i)).

Definition target_pair k (u x : TB.cd k) : B.t :=
  SB.dsum (Nat.pow 2 k) (fun i => B.mul (TB.coord k u i) (TB.coord k x i)).

Lemma h_dsum n g : H.h (SA.dsum n g) = SB.dsum n (fun m => H.h (g m)).
Proof.
  induction n as [|m IH]; cbn [SA.dsum SB.dsum]; [apply H.h_zero | rewrite H.h_add, IH; reflexivity].
Qed.

Lemma h_pair k u x : H.h (source_pair k u x) = target_pair k (tmap k u) (tmap k x).
Proof.
  unfold source_pair, target_pair. rewrite h_dsum. apply SB.dsum_ext. intros m _.
  rewrite H.h_mul, !tmap_coord. reflexivity.
Qed.

Lemma target_dsum_add n g g' :
  SB.dsum n (fun m => B.add (g m) (g' m)) = B.add (SB.dsum n g) (SB.dsum n g').
Proof. induction n as [|m IH]; cbn [SB.dsum]; [ring | rewrite IH; ring]. Qed.

Lemma target_dsum_scale n r g : SB.dsum n (fun m => B.mul r (g m)) = B.mul r (SB.dsum n g).
Proof. induction n as [|m IH]; cbn [SB.dsum]; [ring | rewrite IH; ring]. Qed.

Lemma target_pair_add k u x x' :
  target_pair k u (TB.add k x x') = B.add (target_pair k u x) (target_pair k u x').
Proof.
  unfold target_pair. rewrite <- target_dsum_add. apply SB.dsum_ext. intros m _. rewrite TB.coord_add. ring.
Qed.

Lemma target_pair_scale k u r x : target_pair k u (TB.scale k r x) = B.mul r (target_pair k u x).
Proof.
  unfold target_pair. rewrite <- target_dsum_scale. apply SB.dsum_ext. intros m _. rewrite TB.coord_scale. ring.
Qed.

Lemma target_pair_zero k u : target_pair k u (TB.zero k) = B.zero.
Proof.
  unfold target_pair. rewrite <- (SB.dsum_zero (Nat.pow 2 k)). apply SB.dsum_ext. intros m _.
  rewrite TB.coord_zero. ring.
Qed.

Lemma target_pair_tsum k u n g :
  target_pair k u (SB.tsum k n g) = SB.dsum n (fun m => target_pair k u (g m)).
Proof.
  induction n as [|m IH]; cbn [SB.tsum SB.dsum]; [apply target_pair_zero | rewrite target_pair_add, IH; reflexivity].
Qed.

(** The combination sum_j f_j(x) v_j over the source ring and over the target ring. *)
Definition source_comb k n (functionals vectors : nat -> TA.cd k) (x : TA.cd k) : TA.cd k :=
  SA.tsum k n (fun j => TA.scale k (source_pair k (functionals j) x) (vectors j)).

Definition target_comb k n (functionals vectors : nat -> TA.cd k) (x : TB.cd k) : TB.cd k :=
  SB.tsum k n (fun j => TB.scale k (target_pair k (tmap k (functionals j)) x) (tmap k (vectors j))).

Lemma target_comb_tmap k n functionals vectors x :
  target_comb k n functionals vectors (tmap k x) = tmap k (source_comb k n functionals vectors x).
Proof.
  unfold target_comb, source_comb. rewrite tmap_tsum. apply SB.tsum_ext. intros m _.
  rewrite tmap_scale, h_pair. reflexivity.
Qed.

Lemma target_comb_linear k n functionals vectors : SB.linear k (target_comb k n functionals vectors).
Proof.
  split; intros; unfold target_comb; apply TB.ext; intros i _;
    rewrite ?TB.coord_add, ?TB.coord_scale, !SB.coord_tsum.
  - induction n as [|m IH]; cbn [SB.dsum]; [ring |].
    rewrite IH, !TB.coord_scale, target_pair_add. ring.
  - induction n as [|m IH]; cbn [SB.dsum]; [ring |].
    rewrite IH, !TB.coord_scale, target_pair_scale. ring.
Qed.

Section Certificate.

Variables (k n : nat) (y : TA.cd k) (d : A.t) (back functionals vectors : nat -> TA.cd k).

Hypothesis vectors_annihilated : forall j, (j < n)%nat -> TA.mul k y (vectors j) = TA.zero k.

Hypothesis splitting_on_basis : forall i, (i < Nat.pow 2 k)%nat ->
  TA.scale k d (SA.basis k i) =
  TA.add k (source_map k back (TA.mul k y (SA.basis k i))) (source_comb k n functionals vectors (SA.basis k i)).

Hypothesis functionals_dual : forall j l, (j < n)%nat -> (l < n)%nat ->
  source_pair k (functionals j) (vectors l) = if Nat.eqb j l then d else A.zero.

(** The vectors lie in the kernel over the target ring. *)
Theorem kernel_vectors : forall j, (j < n)%nat -> TB.mul k (tmap k y) (tmap k (vectors j)) = TB.zero k.
Proof.
  intros j Hj. rewrite <- tmap_mul, vectors_annihilated by assumption. apply tmap_zero.
Qed.

Theorem combination_annihilated (a : nat -> B.t) :
  TB.mul k (tmap k y) (SB.tsum k n (fun j => TB.scale k (a j) (tmap k (vectors j)))) = TB.zero k.
Proof.
  assert (L : SB.linear k (TB.mul k (tmap k y))) by exact (proj2 (SB.mul_bilinear k) (tmap k y)).
  rewrite (SB.linear_tsum k _ n _ L).
  rewrite (SB.tsum_ext k n _ (fun _ => TB.zero k)).
  - clear. induction n as [|m IH]; cbn [SB.tsum]; [reflexivity |]. rewrite IH. apply TB.ext. intros i _.
    rewrite TB.coord_add, TB.coord_zero. ring.
  - intros m Hm. rewrite (proj2 L), kernel_vectors by assumption. apply TB.ext. intros i _.
    rewrite TB.coord_scale, TB.coord_zero. ring.
Qed.

(** h(d) z = back(y z) + sum_j f_j(z) v_j for every z over the target ring. *)
Theorem splitting : forall z,
  TB.scale k (H.h d) z =
  TB.add k (target_map k back (TB.mul k (tmap k y) z)) (target_comb k n functionals vectors z).
Proof.
  assert (M : SB.linear k (TB.mul k (tmap k y))) by exact (proj2 (SB.mul_bilinear k) (tmap k y)).
  destruct M as [Ma Ms].
  destruct (target_map_linear k back) as [Ba Bs].
  destruct (target_comb_linear k n functionals vectors) as [Ca Cs].
  apply (SB.linear_ext k (fun z => TB.scale k (H.h d) z)
           (fun z => TB.add k (target_map k back (TB.mul k (tmap k y) z)) (target_comb k n functionals vectors z))).
  - split; intros; apply TB.ext; intros i _;
      repeat (rewrite TB.coord_add || rewrite TB.coord_scale); ring.
  - split; intros.
    + rewrite Ma, Ba, Ca. apply TB.ext. intros i _. repeat rewrite TB.coord_add. ring.
    + rewrite Ms, Bs, Cs. apply TB.ext. intros i _.
      repeat (rewrite TB.coord_add || rewrite TB.coord_scale). ring.
  - intros i Hi.
    rewrite <- tmap_basis, <- tmap_mul, target_map_tmap, target_comb_tmap, <- tmap_add, <- tmap_scale.
    f_equal. apply splitting_on_basis. assumption.
Qed.

(** Every element of the kernel is, after multiplication by h(d), a combination of the vectors. *)
Theorem kernel_spanned : forall z, TB.mul k (tmap k y) z = TB.zero k ->
  TB.scale k (H.h d) z = target_comb k n functionals vectors z.
Proof.
  intros z Hz. rewrite splitting, Hz, (SB.linear_zero k _ (target_map_linear k back)).
  apply TB.ext. intros i _. rewrite TB.coord_add, TB.coord_zero. ring.
Qed.

(** The functionals read the coefficients of a combination back, multiplied by h(d). *)
Theorem coefficients_recovered (a : nat -> B.t) : forall l, (l < n)%nat ->
  target_pair k (tmap k (functionals l)) (SB.tsum k n (fun j => TB.scale k (a j) (tmap k (vectors j)))) =
  B.mul (H.h d) (a l).
Proof.
  intros l Hl. rewrite target_pair_tsum.
  rewrite (SB.dsum_ext n _ (fun j => B.mul (B.mul (H.h d) (a j)) (if Nat.eqb j l then B.one else B.zero))).
  - rewrite SB.dsum_delta. rewrite (proj2 (Nat.ltb_lt _ _) Hl). reflexivity.
  - intros m Hm. rewrite target_pair_scale, <- h_pair, functionals_dual by assumption.
    rewrite (Nat.eqb_sym l m). destruct (Nat.eqb m l); [ring | rewrite H.h_zero; ring].
Qed.

(** With an inverse of h(d), the kernel is the free module on the vectors: an element lies in the kernel
    exactly when it equals the combination with coefficients inverse f_j(z), and the coefficients of a
    combination are unique. *)
Section InvertibleScalar.

Variable inverse : B.t.
Hypothesis inverse_law : B.mul (H.h d) inverse = B.one.

Theorem kernel_free_basis : forall z,
  TB.mul k (tmap k y) z = TB.zero k <->
  z = SB.tsum k n (fun j => TB.scale k (B.mul inverse (target_pair k (tmap k (functionals j)) z)) (tmap k (vectors j))).
Proof.
  intro z. split.
  - intro Hz. pose proof (kernel_spanned z Hz) as E. apply TB.ext. intros i _.
    apply (f_equal (fun w => TB.coord k w i)) in E. unfold target_comb in E.
    rewrite TB.coord_scale, SB.coord_tsum in E. rewrite SB.coord_tsum.
    transitivity (B.mul inverse (B.mul (H.h d) (TB.coord k z i))).
    + transitivity (B.mul (B.mul (H.h d) inverse) (TB.coord k z i)); [rewrite inverse_law; ring | ring].
    + rewrite E, <- target_dsum_scale. apply SB.dsum_ext. intros m _. rewrite !TB.coord_scale. ring.
  - intro E. rewrite E. apply combination_annihilated.
Qed.

Theorem kernel_coefficients_unique (a : nat -> B.t) : forall l, (l < n)%nat ->
  a l = B.mul inverse
          (target_pair k (tmap k (functionals l)) (SB.tsum k n (fun j => TB.scale k (a j) (tmap k (vectors j))))).
Proof.
  intros l Hl. rewrite coefficients_recovered by assumption.
  transitivity (B.mul (B.mul (H.h d) inverse) (a l)); [rewrite inverse_law; ring | ring].
Qed.

End InvertibleScalar.

End Certificate.

End KernelCertificate.
