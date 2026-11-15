(** Real kernels of the canonical A_5 points, in the open tower.

    CdTowerCanonicalKernels.v states, for each of twelve points of A_5, that
    the kernel of left multiplication is free of rank 8, 12 or 16 over every
    commutative ring D in which the image of d (2, or 50 for the point V) is
    invertible, in the coordinate tower of CdTowerRing.v. This source takes
    D to be the real field of CdTowerDomain.RDomain and carries the statement
    to OpenGororoba.RecursiveCDTower.cd_tower 5 through TowerBridge.v.

    What the bridge supplies: to_quantum is a bijection of cd_tower k onto
    the quantum tower with inverse of_quantum (of_to_quantum, to_of_quantum),
    it preserves zero, sum and scalar multiples, and it preserves the product
    (to_quantum_mul). A statement about the product of the open tower and its
    zero therefore transports in both directions, which open_free_of_certificate
    does once for all points: a family w of the quantum tower with
    - y (sum_j a_j w_j) = 0 for every coefficient family a,
    - a vanishing combination has h(d) a_j = 0 and h(d) invertible,
    - every z with y z = 0 equal to some combination,
    gives the same three facts for of_quantum y and the vectors of_quantum
    (w_j) in the open tower. left_kernel_free k n p states them: the
    vectors of_quantum (w_j) have the combinations as the kernel of left
    multiplication by p (every combination is in it, every element of it is
    one) and the combination is zero only for the zero coefficients, so the
    kernel is the free R-module on n vectors, of dimension n.

    The point is stated in the open tower as the sum of its terms c e_a, e_a
    the open basis unit tower_basis 5 (cube_decode 5 a), a the coordinate
    index of of_list in CdTowerCanonicalKernels.v (first half first: the top
    bit of the index selects the second pair component, as in Tower.e of
    lean/GororobaMath/CayleyDickson/Tower.lean). open_vec_eq proves that this sum is
    of_quantum of the real image of the integer point: the coordinates are
    compared as integers by vm_compute, and the real image of an integer c is
    IZR c (h_IZR).

    Each point of the twelve has a theorem NAME_open_kernel_free, and
    E1E18_open_kernel_free is the same statement for e_1 + e_18, whose
    certificate is CdTowerE1E18Kernel.v, so that the kernel of e_1 + e_18
    of A_5 is free of rank 12 over the reals. The ranks are 8 (W8, Ehat,
    Iso, Xp, Xm), 12 (B9, V, VB, Vap, Vam, E1E18) and 16 (Np, Nm). The
    statements rest on two axioms, sig_forall_dec of the Stdlib real-number
    construction and functional_extensionality_dep, both already in
    kernel-assumptions.txt. *)

From Stdlib Require Import Reals ZArith List Lia PeanoNat Ring.
From OpenGororoba Require Import RecursiveCDTower CDSignNumericCorrespondence CDTowerSignCorrespondence.
Require Import CdTowerDomain CdTowerRing CdTowerRingBasis CdTowerRingBaseChange.
Require TowerBridge CdTowerCanonicalKernels CdTowerE1E18Kernel.
Import ListNotations.

Module Q := CdTowerDomain.RTower.
Module RK := CdTowerCanonicalKernels.CanonicalKernels CdTowerDomain.RDomain.
Module RE := CdTowerE1E18Kernel.E1E18Kernel CdTowerDomain.RDomain.
Abbreviation to_quantum := TowerBridge.to_quantum.
Abbreviation of_quantum := TowerBridge.of_quantum.
Abbreviation tmap := RK.KC.BC.tmap.

Tactic Notation "below" integer(bound) tactic3(run) :=
  let j := fresh "j" in let Hj := fresh "Hj" in
  intros j Hj; do bound (destruct j as [|j]; [run |]); exfalso; lia.

(** The bridge is injective, and carries combinations. *)

Lemma to_quantum_inj k x y : to_quantum k x = to_quantum k y -> x = y.
Proof. intro E. rewrite <- (TowerBridge.of_to_quantum k x), <- (TowerBridge.of_to_quantum k y), E. reflexivity. Qed.

Fixpoint open_comb k n (a : nat -> R) (v : nat -> cd_tower k) : cd_tower k :=
  match n with
  | O => tower_zero k
  | S m => tower_add k (open_comb k m a v) (tower_scale k (a m) (v m))
  end.

Fixpoint qcomb k n (a : nat -> R) (w : nat -> Q.cd k) : Q.cd k :=
  match n with
  | O => Q.zero k
  | S m => Q.add k (qcomb k m a w) (Q.scale k (a m) (w m))
  end.

Lemma to_quantum_open_comb k n a (w : nat -> Q.cd k) :
  to_quantum k (open_comb k n a (fun j => of_quantum k (w j))) = qcomb k n a w.
Proof.
  induction n as [|m IH]; cbn [open_comb qcomb]; [apply TowerBridge.to_quantum_zero |].
  rewrite TowerBridge.to_quantum_add, IH, TowerBridge.to_quantum_scale, TowerBridge.to_of_quantum. reflexivity.
Qed.

(** The kernel of left multiplication by p on cd_tower k is the free module of rank n on a family v. *)
Definition left_kernel_free (k n : nat) (p : cd_tower k) : Prop :=
  exists v : nat -> cd_tower k,
    (forall a, tower_mul k p (open_comb k n a v) = tower_zero k) /\
    (forall a, open_comb k n a v = tower_zero k -> forall j, (j < n)%nat -> a j = 0%R) /\
    (forall z, tower_mul k p z = tower_zero k -> exists a, z = open_comb k n a v).

Module SB := RK.KC.BC.SB.
Module TB := RK.KC.BC.TB.

Lemma qcomb_tsum k n a (w : nat -> Q.cd k) :
  qcomb k n a w = SB.tsum k n (fun j => TB.scale k (a j) (w j)).
Proof. induction n as [|m IH]; cbn [qcomb SB.tsum]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma open_free_of_certificate k n (y : Q.cd k) (w : nat -> Q.cd k) (hd inv : R) :
  (hd * inv = 1)%R ->
  (forall a, TB.mul k y (SB.tsum k n (fun j => TB.scale k (a j) (w j))) = TB.zero k) ->
  (forall a l, (l < n)%nat -> SB.tsum k n (fun j => TB.scale k (a j) (w j)) = TB.zero k -> (hd * a l = 0)%R) ->
  (forall z, TB.mul k y z = TB.zero k -> exists a, z = SB.tsum k n (fun j => TB.scale k (a j) (w j))) ->
  left_kernel_free k n (of_quantum k y).
Proof.
  intros HI HA0 HR0 HS0.
  assert (HA : forall a, Q.mul k y (qcomb k n a w) = Q.zero k).
  { intro a. rewrite qcomb_tsum. exact (HA0 a). }
  assert (HR : forall a l, (l < n)%nat -> qcomb k n a w = Q.zero k -> (hd * a l = 0)%R).
  { intros a l Hl E. apply (HR0 a l Hl). rewrite <- qcomb_tsum. exact E. }
  assert (HS : forall z, Q.mul k y z = Q.zero k -> exists a, z = qcomb k n a w).
  { intros z Hz. destruct (HS0 z Hz) as [a Ha]. exists a. rewrite qcomb_tsum. exact Ha. }
  exists (fun j => of_quantum k (w j)). split; [|split].
  - intro a. apply to_quantum_inj.
    rewrite TowerBridge.to_quantum_mul, TowerBridge.to_of_quantum, to_quantum_open_comb, TowerBridge.to_quantum_zero.
    apply HA.
  - intros a E l Hl.
    assert (Z0 : qcomb k n a w = Q.zero k).
    { rewrite <- to_quantum_open_comb, E. apply TowerBridge.to_quantum_zero. }
    pose proof (HR a l Hl Z0) as H0.
    transitivity (inv * (hd * a l))%R; [| rewrite H0; ring].
    transitivity ((hd * inv) * a l)%R; [rewrite HI; ring | ring].
  - intros z Hz. apply (f_equal (to_quantum k)) in Hz.
    rewrite TowerBridge.to_quantum_mul, TowerBridge.to_of_quantum, TowerBridge.to_quantum_zero in Hz.
    destruct (HS _ Hz) as [a Ha]. exists a. apply to_quantum_inj. rewrite to_quantum_open_comb. exact Ha.
Qed.

(** The real image of an integer is its embedding. *)
Module HR := IntegerHom CdTowerDomain.RDomain.

Lemma h_IZR z : HR.h z = IZR z.
Proof.
  assert (pos : forall p, HR.h (Zpos p) = IZR (Zpos p)).
  { induction p as [|p IH] using Pos.peano_ind.
    - exact HR.h_one.
    - rewrite Pos2Z.inj_succ, <- Z.add_1_r.
      change (HR.h (IntegerRing.add (Zpos p) 1) = IZR (Zpos p + 1)). rewrite HR.h_add, IH, plus_IZR. change (HR.h 1) with (HR.h IntegerRing.one). rewrite HR.h_one. reflexivity. }
  destruct z as [|p|p]; [exact HR.h_zero | apply pos |].
  change (HR.h (IntegerRing.opp (Zpos p)) = IZR (- Zpos p)). rewrite HR.h_opp, pos, opp_IZR. reflexivity.
Qed.

Lemma inverse_law (d : Z) : (d <> 0)%Z -> (RK.H.h d * / IZR d = 1)%R.
Proof.
  intro nz. change (RK.H.h d) with (HR.h d). rewrite h_IZR. apply Rinv_r, not_0_IZR. exact nz.
Qed.

(** Points of the open tower as sums of terms c e_a. *)
Definition open_vec (terms : list (nat * Z)) : cd_tower 5 :=
  fold_right (fun t acc => tower_add 5 (tower_scale 5 (IZR (snd t)) (tower_basis 5 (cube_decode 5 (fst t)))) acc)
    (tower_zero 5) terms.

Fixpoint zcoord (terms : list (nat * Z)) (i : nat) : Z :=
  match terms with
  | [] => 0%Z
  | t :: rest => ((if Nat.eqb i (fst t) then snd t else 0) + zcoord rest i)%Z
  end.

Lemma open_vec_coord terms : Forall (fun t => (fst t < 32)%nat) terms -> forall i, (i < 32)%nat ->
  Q.coord 5 (to_quantum 5 (open_vec terms)) i = IZR (zcoord terms i).
Proof.
  intros Hb i Hi. induction terms as [|t rest IH]; cbn [open_vec fold_right zcoord].
  - rewrite TowerBridge.to_quantum_zero, Q.coord_zero. reflexivity.
  - inversion Hb as [|? ? Ht Hr]; subst.
    rewrite TowerBridge.to_quantum_add, Q.coord_add, TowerBridge.to_quantum_scale, Q.coord_scale,
      TowerBridge.to_quantum_basis, TowerBridge.quantum_unit_coord by (cbn; lia).
    unfold CdTowerDomain.RDomain.add, CdTowerDomain.RDomain.mul.
    rewrite plus_IZR. f_equal.
    + destruct (Nat.eqb i (fst t)); [rewrite Rmult_1_r | rewrite Rmult_0_r]; reflexivity.
    + apply IH. exact Hr.
Qed.

Lemma open_vec_eq terms (y : RK.KC.BC.TA.cd 5) : Forall (fun t => (fst t < 32)%nat) terms ->
  (forall i, (i < 32)%nat -> zcoord terms i = RK.KC.BC.TA.coord 5 y i) ->
  open_vec terms = of_quantum 5 (tmap 5 y).
Proof.
  intros Hb E. apply to_quantum_inj. rewrite TowerBridge.to_of_quantum. apply Q.ext. intros i Hi.
  rewrite open_vec_coord by (assumption || (cbn in Hi; lia)).
  rewrite <- RK.KC.BC.tmap_coord, h_IZR. cbn in Hi. rewrite E by lia. reflexivity.
Qed.


(** RK.KC and RE.KC are applications of KernelCertificate at different module paths. Measured (Rocq 9.3.0): a
    closed-term conversion of a statement of one with the same statement of the other, such as the type of
    RE.vectors_annihilated read at the operations of RK.KC, did not finish in 10 s, and each operation of the
    two instances is equal to the other as a function by reflexivity. The point E1E18 moves between the
    instances by rewriting with those equations. *)
Lemma mulE : RK.KC.BC.TB.mul = RE.KC.BC.TB.mul. Proof. reflexivity. Qed.
Lemma zeroE : RK.KC.BC.TB.zero = RE.KC.BC.TB.zero. Proof. reflexivity. Qed.
Lemma scaleE : RK.KC.BC.TB.scale = RE.KC.BC.TB.scale. Proof. reflexivity. Qed.
Lemma tsumE : RK.KC.BC.SB.tsum = RE.KC.BC.SB.tsum. Proof. reflexivity. Qed.
Lemma tmapE : RK.KC.BC.tmap = RE.KC.BC.tmap. Proof. reflexivity. Qed.

(** The twelve points of CdTowerCanonicalKernels.v and e_1 + e_18, in the open tower. *)
Definition W8_terms : list (nat * Z) := [(17%nat, 1%Z); (27%nat, (-1)%Z)].

Lemma W8_open_point : open_vec W8_terms = of_quantum 5 (tmap 5 RK.W8_point).
Proof. apply open_vec_eq. { repeat constructor; cbn; lia. } below 32 (vm_compute; reflexivity). Qed.

Theorem W8_open_kernel_free : left_kernel_free 5 8 (open_vec W8_terms).
Proof.
  rewrite W8_open_point.
  apply (open_free_of_certificate 5 8 (tmap 5 RK.W8_point) (fun j => tmap 5 (RK.W8_vectors j)) (RK.H.h 2) (/ IZR 2%Z)%R).
  - exact (inverse_law 2%Z ltac:(discriminate)).
  - intro a. exact (RK.KC.combination_annihilated 5 8 RK.W8_point RK.W8_vectors RK.W8_vectors_annihilated a).
  - intros a l Hl E. exact (RK.W8_combination_zero_coefficients a E l Hl).
  - intros z Hz. refine (ex_intro _ (fun j => (/ IZR 2%Z * RK.KC.target_pair 5 (tmap 5 (RK.W8_functionals j)) z)%R) _).
    exact (proj1 (RK.W8_kernel_free_basis (/ IZR 2%Z)%R (inverse_law 2%Z ltac:(discriminate)) z) Hz).
Qed.

Definition Ehat_terms : list (nat * Z) := [(3%nat, (-1)%Z); (9%nat, (-5)%Z); (10%nat, (-2)%Z); (17%nat, 3%Z); (18%nat, 1%Z); (24%nat, 4%Z); (27%nat, (-2)%Z)].

Lemma Ehat_open_point : open_vec Ehat_terms = of_quantum 5 (tmap 5 RK.Ehat_point).
Proof. apply open_vec_eq. { repeat constructor; cbn; lia. } below 32 (vm_compute; reflexivity). Qed.

Theorem Ehat_open_kernel_free : left_kernel_free 5 8 (open_vec Ehat_terms).
Proof.
  rewrite Ehat_open_point.
  apply (open_free_of_certificate 5 8 (tmap 5 RK.Ehat_point) (fun j => tmap 5 (RK.Ehat_vectors j)) (RK.H.h 2) (/ IZR 2%Z)%R).
  - exact (inverse_law 2%Z ltac:(discriminate)).
  - intro a. exact (RK.KC.combination_annihilated 5 8 RK.Ehat_point RK.Ehat_vectors RK.Ehat_vectors_annihilated a).
  - intros a l Hl E. exact (RK.Ehat_combination_zero_coefficients a E l Hl).
  - intros z Hz. refine (ex_intro _ (fun j => (/ IZR 2%Z * RK.KC.target_pair 5 (tmap 5 (RK.Ehat_functionals j)) z)%R) _).
    exact (proj1 (RK.Ehat_kernel_free_basis (/ IZR 2%Z)%R (inverse_law 2%Z ltac:(discriminate)) z) Hz).
Qed.

Definition Iso_terms : list (nat * Z) := [(3%nat, (-1)%Z); (10%nat, (-1)%Z); (17%nat, 1%Z); (29%nat, (-1)%Z)].

Lemma Iso_open_point : open_vec Iso_terms = of_quantum 5 (tmap 5 RK.Iso_point).
Proof. apply open_vec_eq. { repeat constructor; cbn; lia. } below 32 (vm_compute; reflexivity). Qed.

Theorem Iso_open_kernel_free : left_kernel_free 5 8 (open_vec Iso_terms).
Proof.
  rewrite Iso_open_point.
  apply (open_free_of_certificate 5 8 (tmap 5 RK.Iso_point) (fun j => tmap 5 (RK.Iso_vectors j)) (RK.H.h 2) (/ IZR 2%Z)%R).
  - exact (inverse_law 2%Z ltac:(discriminate)).
  - intro a. exact (RK.KC.combination_annihilated 5 8 RK.Iso_point RK.Iso_vectors RK.Iso_vectors_annihilated a).
  - intros a l Hl E. exact (RK.Iso_combination_zero_coefficients a E l Hl).
  - intros z Hz. refine (ex_intro _ (fun j => (/ IZR 2%Z * RK.KC.target_pair 5 (tmap 5 (RK.Iso_functionals j)) z)%R) _).
    exact (proj1 (RK.Iso_kernel_free_basis (/ IZR 2%Z)%R (inverse_law 2%Z ltac:(discriminate)) z) Hz).
Qed.

Definition Xp_terms : list (nat * Z) := [(3%nat, (-1)%Z); (9%nat, (-1)%Z); (17%nat, 1%Z); (18%nat, 1%Z)].

Lemma Xp_open_point : open_vec Xp_terms = of_quantum 5 (tmap 5 RK.Xp_point).
Proof. apply open_vec_eq. { repeat constructor; cbn; lia. } below 32 (vm_compute; reflexivity). Qed.

Theorem Xp_open_kernel_free : left_kernel_free 5 8 (open_vec Xp_terms).
Proof.
  rewrite Xp_open_point.
  apply (open_free_of_certificate 5 8 (tmap 5 RK.Xp_point) (fun j => tmap 5 (RK.Xp_vectors j)) (RK.H.h 2) (/ IZR 2%Z)%R).
  - exact (inverse_law 2%Z ltac:(discriminate)).
  - intro a. exact (RK.KC.combination_annihilated 5 8 RK.Xp_point RK.Xp_vectors RK.Xp_vectors_annihilated a).
  - intros a l Hl E. exact (RK.Xp_combination_zero_coefficients a E l Hl).
  - intros z Hz. refine (ex_intro _ (fun j => (/ IZR 2%Z * RK.KC.target_pair 5 (tmap 5 (RK.Xp_functionals j)) z)%R) _).
    exact (proj1 (RK.Xp_kernel_free_basis (/ IZR 2%Z)%R (inverse_law 2%Z ltac:(discriminate)) z) Hz).
Qed.

Definition Xm_terms : list (nat * Z) := [(3%nat, (-1)%Z); (9%nat, 1%Z); (17%nat, 1%Z); (18%nat, 1%Z)].

Lemma Xm_open_point : open_vec Xm_terms = of_quantum 5 (tmap 5 RK.Xm_point).
Proof. apply open_vec_eq. { repeat constructor; cbn; lia. } below 32 (vm_compute; reflexivity). Qed.

Theorem Xm_open_kernel_free : left_kernel_free 5 8 (open_vec Xm_terms).
Proof.
  rewrite Xm_open_point.
  apply (open_free_of_certificate 5 8 (tmap 5 RK.Xm_point) (fun j => tmap 5 (RK.Xm_vectors j)) (RK.H.h 2) (/ IZR 2%Z)%R).
  - exact (inverse_law 2%Z ltac:(discriminate)).
  - intro a. exact (RK.KC.combination_annihilated 5 8 RK.Xm_point RK.Xm_vectors RK.Xm_vectors_annihilated a).
  - intros a l Hl E. exact (RK.Xm_combination_zero_coefficients a E l Hl).
  - intros z Hz. refine (ex_intro _ (fun j => (/ IZR 2%Z * RK.KC.target_pair 5 (tmap 5 (RK.Xm_functionals j)) z)%R) _).
    exact (proj1 (RK.Xm_kernel_free_basis (/ IZR 2%Z)%R (inverse_law 2%Z ltac:(discriminate)) z) Hz).
Qed.

Definition B9_terms : list (nat * Z) := [(3%nat, (-1)%Z); (6%nat, (-2)%Z); (9%nat, (-3)%Z); (12%nat, (-5)%Z); (17%nat, 1%Z); (20%nat, 2%Z); (27%nat, (-3)%Z); (30%nat, (-5)%Z)].

Lemma B9_open_point : open_vec B9_terms = of_quantum 5 (tmap 5 RK.B9_point).
Proof. apply open_vec_eq. { repeat constructor; cbn; lia. } below 32 (vm_compute; reflexivity). Qed.

Theorem B9_open_kernel_free : left_kernel_free 5 12 (open_vec B9_terms).
Proof.
  rewrite B9_open_point.
  apply (open_free_of_certificate 5 12 (tmap 5 RK.B9_point) (fun j => tmap 5 (RK.B9_vectors j)) (RK.H.h 2) (/ IZR 2%Z)%R).
  - exact (inverse_law 2%Z ltac:(discriminate)).
  - intro a. exact (RK.KC.combination_annihilated 5 12 RK.B9_point RK.B9_vectors RK.B9_vectors_annihilated a).
  - intros a l Hl E. exact (RK.B9_combination_zero_coefficients a E l Hl).
  - intros z Hz. refine (ex_intro _ (fun j => (/ IZR 2%Z * RK.KC.target_pair 5 (tmap 5 (RK.B9_functionals j)) z)%R) _).
    exact (proj1 (RK.B9_kernel_free_basis (/ IZR 2%Z)%R (inverse_law 2%Z ltac:(discriminate)) z) Hz).
Qed.

Definition V_terms : list (nat * Z) := [(9%nat, (-5)%Z); (17%nat, 3%Z); (24%nat, 4%Z)].

Lemma V_open_point : open_vec V_terms = of_quantum 5 (tmap 5 RK.V_point).
Proof. apply open_vec_eq. { repeat constructor; cbn; lia. } below 32 (vm_compute; reflexivity). Qed.

Theorem V_open_kernel_free : left_kernel_free 5 12 (open_vec V_terms).
Proof.
  rewrite V_open_point.
  apply (open_free_of_certificate 5 12 (tmap 5 RK.V_point) (fun j => tmap 5 (RK.V_vectors j)) (RK.H.h 50) (/ IZR 50%Z)%R).
  - exact (inverse_law 50%Z ltac:(discriminate)).
  - intro a. exact (RK.KC.combination_annihilated 5 12 RK.V_point RK.V_vectors RK.V_vectors_annihilated a).
  - intros a l Hl E. exact (RK.V_combination_zero_coefficients a E l Hl).
  - intros z Hz. refine (ex_intro _ (fun j => (/ IZR 50%Z * RK.KC.target_pair 5 (tmap 5 (RK.V_functionals j)) z)%R) _).
    exact (proj1 (RK.V_kernel_free_basis (/ IZR 50%Z)%R (inverse_law 50%Z ltac:(discriminate)) z) Hz).
Qed.

Definition VB_terms : list (nat * Z) := [(3%nat, (-1)%Z); (17%nat, 1%Z)].

Lemma VB_open_point : open_vec VB_terms = of_quantum 5 (tmap 5 RK.VB_point).
Proof. apply open_vec_eq. { repeat constructor; cbn; lia. } below 32 (vm_compute; reflexivity). Qed.

Theorem VB_open_kernel_free : left_kernel_free 5 12 (open_vec VB_terms).
Proof.
  rewrite VB_open_point.
  apply (open_free_of_certificate 5 12 (tmap 5 RK.VB_point) (fun j => tmap 5 (RK.VB_vectors j)) (RK.H.h 2) (/ IZR 2%Z)%R).
  - exact (inverse_law 2%Z ltac:(discriminate)).
  - intro a. exact (RK.KC.combination_annihilated 5 12 RK.VB_point RK.VB_vectors RK.VB_vectors_annihilated a).
  - intros a l Hl E. exact (RK.VB_combination_zero_coefficients a E l Hl).
  - intros z Hz. refine (ex_intro _ (fun j => (/ IZR 2%Z * RK.KC.target_pair 5 (tmap 5 (RK.VB_functionals j)) z)%R) _).
    exact (proj1 (RK.VB_kernel_free_basis (/ IZR 2%Z)%R (inverse_law 2%Z ltac:(discriminate)) z) Hz).
Qed.

Definition Vap_terms : list (nat * Z) := [(9%nat, (-1)%Z); (17%nat, 1%Z)].

Lemma Vap_open_point : open_vec Vap_terms = of_quantum 5 (tmap 5 RK.Vap_point).
Proof. apply open_vec_eq. { repeat constructor; cbn; lia. } below 32 (vm_compute; reflexivity). Qed.

Theorem Vap_open_kernel_free : left_kernel_free 5 12 (open_vec Vap_terms).
Proof.
  rewrite Vap_open_point.
  apply (open_free_of_certificate 5 12 (tmap 5 RK.Vap_point) (fun j => tmap 5 (RK.Vap_vectors j)) (RK.H.h 2) (/ IZR 2%Z)%R).
  - exact (inverse_law 2%Z ltac:(discriminate)).
  - intro a. exact (RK.KC.combination_annihilated 5 12 RK.Vap_point RK.Vap_vectors RK.Vap_vectors_annihilated a).
  - intros a l Hl E. exact (RK.Vap_combination_zero_coefficients a E l Hl).
  - intros z Hz. refine (ex_intro _ (fun j => (/ IZR 2%Z * RK.KC.target_pair 5 (tmap 5 (RK.Vap_functionals j)) z)%R) _).
    exact (proj1 (RK.Vap_kernel_free_basis (/ IZR 2%Z)%R (inverse_law 2%Z ltac:(discriminate)) z) Hz).
Qed.

Definition Vam_terms : list (nat * Z) := [(9%nat, 1%Z); (17%nat, 1%Z)].

Lemma Vam_open_point : open_vec Vam_terms = of_quantum 5 (tmap 5 RK.Vam_point).
Proof. apply open_vec_eq. { repeat constructor; cbn; lia. } below 32 (vm_compute; reflexivity). Qed.

Theorem Vam_open_kernel_free : left_kernel_free 5 12 (open_vec Vam_terms).
Proof.
  rewrite Vam_open_point.
  apply (open_free_of_certificate 5 12 (tmap 5 RK.Vam_point) (fun j => tmap 5 (RK.Vam_vectors j)) (RK.H.h 2) (/ IZR 2%Z)%R).
  - exact (inverse_law 2%Z ltac:(discriminate)).
  - intro a. exact (RK.KC.combination_annihilated 5 12 RK.Vam_point RK.Vam_vectors RK.Vam_vectors_annihilated a).
  - intros a l Hl E. exact (RK.Vam_combination_zero_coefficients a E l Hl).
  - intros z Hz. refine (ex_intro _ (fun j => (/ IZR 2%Z * RK.KC.target_pair 5 (tmap 5 (RK.Vam_functionals j)) z)%R) _).
    exact (proj1 (RK.Vam_kernel_free_basis (/ IZR 2%Z)%R (inverse_law 2%Z ltac:(discriminate)) z) Hz).
Qed.

Definition Np_terms : list (nat * Z) := [(3%nat, (-1)%Z); (9%nat, (-1)%Z); (17%nat, 1%Z); (27%nat, (-1)%Z)].

Lemma Np_open_point : open_vec Np_terms = of_quantum 5 (tmap 5 RK.Np_point).
Proof. apply open_vec_eq. { repeat constructor; cbn; lia. } below 32 (vm_compute; reflexivity). Qed.

Theorem Np_open_kernel_free : left_kernel_free 5 16 (open_vec Np_terms).
Proof.
  rewrite Np_open_point.
  apply (open_free_of_certificate 5 16 (tmap 5 RK.Np_point) (fun j => tmap 5 (RK.Np_vectors j)) (RK.H.h 2) (/ IZR 2%Z)%R).
  - exact (inverse_law 2%Z ltac:(discriminate)).
  - intro a. exact (RK.KC.combination_annihilated 5 16 RK.Np_point RK.Np_vectors RK.Np_vectors_annihilated a).
  - intros a l Hl E. exact (RK.Np_combination_zero_coefficients a E l Hl).
  - intros z Hz. refine (ex_intro _ (fun j => (/ IZR 2%Z * RK.KC.target_pair 5 (tmap 5 (RK.Np_functionals j)) z)%R) _).
    exact (proj1 (RK.Np_kernel_free_basis (/ IZR 2%Z)%R (inverse_law 2%Z ltac:(discriminate)) z) Hz).
Qed.

Definition Nm_terms : list (nat * Z) := [(3%nat, (-1)%Z); (9%nat, 1%Z); (17%nat, 1%Z); (27%nat, 1%Z)].

Lemma Nm_open_point : open_vec Nm_terms = of_quantum 5 (tmap 5 RK.Nm_point).
Proof. apply open_vec_eq. { repeat constructor; cbn; lia. } below 32 (vm_compute; reflexivity). Qed.

Theorem Nm_open_kernel_free : left_kernel_free 5 16 (open_vec Nm_terms).
Proof.
  rewrite Nm_open_point.
  apply (open_free_of_certificate 5 16 (tmap 5 RK.Nm_point) (fun j => tmap 5 (RK.Nm_vectors j)) (RK.H.h 2) (/ IZR 2%Z)%R).
  - exact (inverse_law 2%Z ltac:(discriminate)).
  - intro a. exact (RK.KC.combination_annihilated 5 16 RK.Nm_point RK.Nm_vectors RK.Nm_vectors_annihilated a).
  - intros a l Hl E. exact (RK.Nm_combination_zero_coefficients a E l Hl).
  - intros z Hz. refine (ex_intro _ (fun j => (/ IZR 2%Z * RK.KC.target_pair 5 (tmap 5 (RK.Nm_functionals j)) z)%R) _).
    exact (proj1 (RK.Nm_kernel_free_basis (/ IZR 2%Z)%R (inverse_law 2%Z ltac:(discriminate)) z) Hz).
Qed.

Definition E1E18_terms : list (nat * Z) := [(1%nat, 1%Z); (18%nat, 1%Z)].

Lemma E1E18_open_point : open_vec E1E18_terms = of_quantum 5 (tmap 5 RE.point).
Proof. apply open_vec_eq. { repeat constructor; cbn; lia. } below 32 (vm_compute; reflexivity). Qed.

Theorem E1E18_open_kernel_free : left_kernel_free 5 12 (open_vec E1E18_terms).
Proof.
  rewrite E1E18_open_point.
  apply (open_free_of_certificate 5 12 (tmap 5 RE.point) (fun j => tmap 5 (RE.vectors j)) (RK.H.h 2) (/ IZR 2%Z)%R).
  - exact (inverse_law 2%Z ltac:(discriminate)).
  - intro a. rewrite mulE, zeroE, tsumE, scaleE, tmapE. exact (RE.KC.combination_annihilated 5 12 RE.point RE.vectors RE.vectors_annihilated a).
  - intros a l Hl E. rewrite tsumE, scaleE, tmapE, zeroE in E. exact (RE.combination_zero_coefficients a E l Hl).
  - intros z Hz. rewrite mulE, zeroE, tmapE in Hz. refine (ex_intro _ (fun j => (/ IZR 2%Z * RE.KC.target_pair 5 (RE.KC.BC.tmap 5 (RE.functionals j)) z)%R) _).
    rewrite tsumE, scaleE, tmapE. exact (proj1 (RE.kernel_free_basis (/ IZR 2%Z)%R (inverse_law 2%Z ltac:(discriminate)) z) Hz).
Qed.

Print Assumptions W8_open_kernel_free.
Print Assumptions Ehat_open_kernel_free.
Print Assumptions Iso_open_kernel_free.
Print Assumptions Xp_open_kernel_free.
Print Assumptions Xm_open_kernel_free.
Print Assumptions B9_open_kernel_free.
Print Assumptions V_open_kernel_free.
Print Assumptions VB_open_kernel_free.
Print Assumptions Vap_open_kernel_free.
Print Assumptions Vam_open_kernel_free.
Print Assumptions Np_open_kernel_free.
Print Assumptions Nm_open_kernel_free.
Print Assumptions E1E18_open_kernel_free.
