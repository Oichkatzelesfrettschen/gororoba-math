From Stdlib Require Import Reals Psatz.

Open Scope R_scope.

Definition binary_channel (false_positive true_positive input_mean : R) : R :=
  false_positive * (1 - input_mean) + true_positive * input_mean.

Theorem binary_channel_contracts_separation :
  forall false_positive true_positive first_mean second_mean,
    0 <= false_positive <= 1 ->
    0 <= true_positive <= 1 ->
    Rabs (binary_channel false_positive true_positive first_mean -
          binary_channel false_positive true_positive second_mean) <=
    Rabs (first_mean - second_mean).
Proof.
  intros false_positive true_positive first_mean second_mean
    [false_positive_lower false_positive_upper]
    [true_positive_lower true_positive_upper].
  unfold binary_channel.
  replace
    (false_positive * (1 - first_mean) + true_positive * first_mean -
     (false_positive * (1 - second_mean) + true_positive * second_mean))
    with ((true_positive - false_positive) * (first_mean - second_mean))
    by ring.
  rewrite Rabs_mult.
  assert (slope_bound : Rabs (true_positive - false_positive) <= 1).
  { apply Rabs_le; split; lra. }
  pose proof (Rmult_le_compat_r (Rabs (first_mean - second_mean))
    (Rabs (true_positive - false_positive)) 1
    (Rabs_pos _) slope_bound) as multiplied_bound.
  lra.
Qed.

Lemma absolute_radius_bounds :
  forall value center radius,
    Rabs (value - center) <= radius ->
    center - radius <= value <= center + radius.
Proof.
  intros value center radius radius_bound.
  pose proof (Rle_abs (value - center)) as upper_bound.
  pose proof (Rle_abs (center - value)) as lower_bound.
  rewrite Rabs_minus_sym in lower_bound.
  split; lra.
Qed.

Definition hardware_first_observed : R := 2964 / 8192.
Definition hardware_third_observed : R := 4911 / 8192.
Definition replay_first_observed : R := 4067 / 8192.
Definition replay_third_observed : R := 4057 / 8192.
Definition mean_radius : R := 21 / 1000.

(* The margin uses exact fractions, independently of a confidence procedure. *)
Theorem observed_separation_margin :
  (hardware_third_observed - hardware_first_observed - 2 * mean_radius) -
  (replay_first_observed - replay_third_observed + 2 * mean_radius) =
  156109 / 1024000.
Proof.
  unfold hardware_first_observed, hardware_third_observed,
    replay_first_observed, replay_third_observed, mean_radius.
  field.
Qed.

(* The four radius hypotheses are deterministic assumptions about real means.
   Neither statistical coverage nor hardware stability is assumed implicitly. *)
Theorem observed_means_exclude_common_binary_channel :
  forall hardware_first hardware_third replay_first replay_third,
    Rabs (hardware_first - hardware_first_observed) <= mean_radius ->
    Rabs (hardware_third - hardware_third_observed) <= mean_radius ->
    Rabs (replay_first - replay_first_observed) <= mean_radius ->
    Rabs (replay_third - replay_third_observed) <= mean_radius ->
    ~ exists false_positive true_positive,
      0 <= false_positive <= 1 /\
      0 <= true_positive <= 1 /\
      hardware_first = binary_channel false_positive true_positive replay_first /\
      hardware_third = binary_channel false_positive true_positive replay_third.
Proof.
  intros hardware_first hardware_third replay_first replay_third
    hardware_first_radius hardware_third_radius
    replay_first_radius replay_third_radius
    [false_positive [true_positive
      [false_positive_bounds [true_positive_bounds [first_channel third_channel]]]]].
  pose proof (binary_channel_contracts_separation
    false_positive true_positive replay_first replay_third
    false_positive_bounds true_positive_bounds) as contraction.
  rewrite <- first_channel, <- third_channel in contraction.
  apply absolute_radius_bounds in hardware_first_radius.
  apply absolute_radius_bounds in hardware_third_radius.
  apply absolute_radius_bounds in replay_first_radius.
  apply absolute_radius_bounds in replay_third_radius.
  destruct hardware_first_radius as [hardware_first_lower hardware_first_upper].
  destruct hardware_third_radius as [hardware_third_lower hardware_third_upper].
  destruct replay_first_radius as [replay_first_lower replay_first_upper].
  destruct replay_third_radius as [replay_third_lower replay_third_upper].
  assert (replay_separation :
    Rabs (replay_first - replay_third) <= 10 / 8192 + 2 * mean_radius).
  { apply Rabs_le.
    unfold replay_first_observed, replay_third_observed, mean_radius in *.
    split; lra. }
  pose proof (Rle_abs (hardware_third - hardware_first)) as hardware_separation.
  rewrite Rabs_minus_sym in hardware_separation.
  unfold hardware_first_observed, hardware_third_observed, mean_radius in *.
  lra.
Qed.

Print Assumptions binary_channel_contracts_separation.
Print Assumptions absolute_radius_bounds.
Print Assumptions observed_separation_margin.
Print Assumptions observed_means_exclude_common_binary_channel.
