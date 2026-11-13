From Stdlib Require Import QArith QArith.Qabs Lqa.

Open Scope Q_scope.

(* Rational equality is Qeq, written ==. All channel identities below use
   that equality; none depend on the representation of a rational number. *)
Definition binary_channel (false_positive true_positive input_mean : Q) : Q :=
  false_positive * (1 - input_mean) + true_positive * input_mean.

Theorem binary_channel_contracts_separation :
  forall false_positive true_positive first_mean second_mean,
    0 <= false_positive <= 1 ->
    0 <= true_positive <= 1 ->
    Qabs (binary_channel false_positive true_positive first_mean -
          binary_channel false_positive true_positive second_mean) <=
    Qabs (first_mean - second_mean).
Proof.
  intros false_positive true_positive first_mean second_mean
    [false_positive_lower false_positive_upper]
    [true_positive_lower true_positive_upper].
  unfold binary_channel.
  setoid_replace
    (false_positive * (1 - first_mean) + true_positive * first_mean -
     (false_positive * (1 - second_mean) + true_positive * second_mean))
    with ((true_positive - false_positive) * (first_mean - second_mean))
    by ring.
  rewrite Qabs_Qmult.
  assert (slope_bound : Qabs (true_positive - false_positive) <= 1).
  { apply Qabs_Qle_condition; split; lra. }
  pose proof (Qmult_le_compat_r _ _ (Qabs (first_mean - second_mean))
    slope_bound (Qabs_nonneg _)) as multiplied_bound.
  lra.
Qed.

Definition hardware_first_observed : Q := 2964 # 8192.
Definition hardware_third_observed : Q := 4911 # 8192.
Definition replay_first_observed : Q := 4067 # 8192.
Definition replay_third_observed : Q := 4057 # 8192.
Definition mean_radius : Q := 21 # 1000.

Theorem observed_separation_margin :
  (hardware_third_observed - hardware_first_observed - 2 * mean_radius) -
  (replay_first_observed - replay_third_observed + 2 * mean_radius) ==
  156109 # 1024000.
Proof. reflexivity. Qed.

(* This theorem assumes deterministic bounds on four unknown rational means.
   Establishing a probability of simultaneous coverage is a separate task. *)
Theorem observed_means_exclude_common_binary_channel :
  forall hardware_first hardware_third replay_first replay_third,
    Qabs (hardware_first - hardware_first_observed) <= mean_radius ->
    Qabs (hardware_third - hardware_third_observed) <= mean_radius ->
    Qabs (replay_first - replay_first_observed) <= mean_radius ->
    Qabs (replay_third - replay_third_observed) <= mean_radius ->
    ~ exists false_positive true_positive,
      0 <= false_positive <= 1 /\
      0 <= true_positive <= 1 /\
      hardware_first == binary_channel false_positive true_positive replay_first /\
      hardware_third == binary_channel false_positive true_positive replay_third.
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
  apply Qabs_Qle_condition in hardware_first_radius.
  apply Qabs_Qle_condition in hardware_third_radius.
  apply Qabs_Qle_condition in replay_first_radius.
  apply Qabs_Qle_condition in replay_third_radius.
  destruct hardware_first_radius as [hardware_first_lower hardware_first_upper].
  destruct hardware_third_radius as [hardware_third_lower hardware_third_upper].
  destruct replay_first_radius as [replay_first_lower replay_first_upper].
  destruct replay_third_radius as [replay_third_lower replay_third_upper].
  assert (replay_separation :
    Qabs (replay_first - replay_third) <= (10 # 8192) + 2 * mean_radius).
  { apply Qabs_Qle_condition.
    unfold replay_first_observed, replay_third_observed, mean_radius in *.
    split; lra. }
  pose proof (Qle_Qabs (hardware_third - hardware_first)) as hardware_separation.
  rewrite Qabs_Qminus in hardware_separation.
  unfold hardware_first_observed, hardware_third_observed, mean_radius in *.
  lra.
Qed.

Print Assumptions binary_channel_contracts_separation.
Print Assumptions observed_separation_margin.
Print Assumptions observed_means_exclude_common_binary_channel.
