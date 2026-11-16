(** * C-872, C-873: finiteness bound of the worldline quadrature.

    Convention: a quadrature is a list of nodes (T, w, theta) with proper
    time T, weight w and boundary indicator theta.  The energy of the
    quadrature is pf times the sum of w * theta / (T * T * sqrt T), the
    algebraic model of the T^{-5/2} worldline integrand of WorldlineBound.v.
    The geometry (pillar in a cavity, sphere in a cylinder) enters only
    through the values theta; this module defines no geometry.

    The module proves: if every node has T >= T_min > 0, w >= 0 and
    |theta| <= B, and the weights sum to T_max - T_min, then the energy is
    bounded in absolute value by
    |pf| * B * (T_max - T_min) / (T_min * T_min * sqrt T_min).
    The bound is the expression whose non-negativity C872_pillar_casimir_finite
    and C873_sphere_casimir_finite state.  The module proves nothing about
    the boundary-crossing probability |theta| <= 1 of either geometry, which
    is the hypothesis B = 1. *)

From Stdlib Require Import List Reals Lra.
From OpenGororoba Require Import Prelude WorldlineBound.
Import ListNotations.

Open Scope R_scope.

Definition wl_node : Type := (R * R * R)%type.

Definition wl_time (q : wl_node) : R := fst (fst q).
Definition wl_weight (q : wl_node) : R := snd (fst q).
Definition wl_theta (q : wl_node) : R := snd q.

Definition wl_summand (q : wl_node) : R :=
  wl_weight q * wl_theta q / (wl_time q * wl_time q * sqrt (wl_time q)).

Definition wl_sum (qs : list wl_node) : R :=
  fold_right (fun q acc => wl_summand q + acc) 0 qs.

Definition wl_total_weight (qs : list wl_node) : R :=
  fold_right (fun q acc => wl_weight q + acc) 0 qs.

Definition wl_energy (pf : R) (qs : list wl_node) : R := pf * wl_sum qs.

(** Every node lies above T_min, has a non-negative weight and a bounded
    indicator. *)
Definition wl_admissible (T_min B : R) (q : wl_node) : Prop :=
  wl_time q >= T_min /\ wl_weight q >= 0 /\ Rabs (wl_theta q) <= B.

Lemma wl_summand_bound : forall (T_min B : R) (q : wl_node),
  T_min > 0 -> wl_admissible T_min B q ->
  Rabs (wl_summand q) <=
    wl_weight q * B / (T_min * T_min * sqrt T_min).
Proof.
  intros T_min B [[T w] theta] HTm [HT [Hw Hth]].
  unfold wl_time, wl_weight, wl_theta in *. simpl in *.
  unfold wl_summand, wl_time, wl_weight, wl_theta. simpl.
  assert (HT0 : T > 0) by lra.
  assert (Hd : T * T * sqrt T > 0) by (apply T_five_halves_pos; exact HT0).
  assert (Hdm : T_min * T_min * sqrt T_min > 0)
    by (apply T_five_halves_pos; exact HTm).
  assert (Hmono := T_five_halves_mono T_min T HTm HT).
  unfold Rdiv. rewrite Rabs_mult, Rabs_inv by (apply Rgt_not_eq; exact Hd).
  rewrite (Rabs_pos_eq (T * T * sqrt T)) by lra.
  rewrite Rabs_mult, (Rabs_pos_eq w) by lra.
  apply Rle_trans with (w * B * / (T * T * sqrt T)).
  - apply Rmult_le_compat_r.
    + left. apply Rinv_0_lt_compat. exact Hd.
    + apply Rmult_le_compat_l; lra.
  - apply Rmult_le_compat_l.
    + apply Rmult_le_pos; [lra |].
      apply Rle_trans with (Rabs theta); [apply Rabs_pos | exact Hth].
    + apply Rinv_le_contravar; lra.
Qed.

Lemma wl_sum_bound : forall (T_min B : R) (qs : list wl_node),
  T_min > 0 -> Forall (wl_admissible T_min B) qs ->
  Rabs (wl_sum qs) <=
    wl_total_weight qs * B / (T_min * T_min * sqrt T_min).
Proof.
  intros T_min B qs HTm Hall.
  assert (Hdm : T_min * T_min * sqrt T_min > 0)
    by (apply T_five_halves_pos; exact HTm).
  induction Hall as [| q qs Hq Hqs IH].
  - simpl. unfold Rdiv. rewrite Rabs_R0. rewrite Rmult_0_l, Rmult_0_l. lra.
  - simpl.
    apply Rle_trans with (Rabs (wl_summand q) + Rabs (fold_right
      (fun q0 acc => wl_summand q0 + acc) 0 qs)).
    + apply Rabs_triang.
    + assert (Hs := wl_summand_bound T_min B q HTm Hq).
      unfold wl_sum in IH.
      assert (Hdiv : forall a b : R,
        (a + b) * B / (T_min * T_min * sqrt T_min) =
        a * B / (T_min * T_min * sqrt T_min) +
        b * B / (T_min * T_min * sqrt T_min)).
      { intros a b. unfold Rdiv. ring. }
      rewrite Hdiv. lra.
Qed.

(** The worldline energy of any admissible quadrature is bounded by the
    expression of WorldlineBound.v. *)
Theorem worldline_quadrature_energy_bound :
  forall (T_min T_max B pf : R) (qs : list wl_node),
    T_min > 0 -> T_max > T_min -> B >= 0 ->
    Forall (wl_admissible T_min B) qs ->
    wl_total_weight qs = T_max - T_min ->
    Rabs (wl_energy pf qs) <=
      Rabs pf * B * (T_max - T_min) / (T_min * T_min * sqrt T_min).
Proof.
  intros T_min T_max B pf qs HTm HTM HB Hall Hw.
  unfold wl_energy. rewrite Rabs_mult.
  pose proof (wl_sum_bound T_min B qs HTm Hall) as Hs.
  rewrite Hw in Hs.
  assert (Hdm : T_min * T_min * sqrt T_min > 0)
    by (apply T_five_halves_pos; exact HTm).
  assert (Hrw : Rabs pf * B * (T_max - T_min) / (T_min * T_min * sqrt T_min) =
                Rabs pf * ((T_max - T_min) * B / (T_min * T_min * sqrt T_min))).
  { unfold Rdiv. ring. }
  rewrite Hrw.
  apply Rmult_le_compat_l; [apply Rabs_pos | exact Hs].
Qed.
