(** The quantum terminal-channel theorems, rational and real, each proved by
    one instantiation of the general theorem of the open tree: the hardware
    means are the outputs, the replay means the inputs, the observed
    fractions the centers and mean_radius all four radii. Each statement
    proved here is the type of the quantum theorem itself, read with
    [type of], so it carries the quantum [binary_channel]; the open theorem
    concludes with the open [binary_channel], and the two constants have
    the same body, so the instantiation closes by conversion. The open
    libraries are required before the quantum ones: the quantum libraries
    carry the empty logical root, and requiring them first makes the open
    short names mask their absolute names (warning masking-absolute-name,
    in the default set). *)

From Stdlib Require Import QArith QArith.Qabs Lqa Reals Psatz.
From OpenGororoba Require TerminalChannelSeparation TerminalChannelSeparationReal.
Require TerminalChannelSeparation TerminalChannelSeparationReal.

Locate Library TerminalChannelSeparation.
Locate Library OpenGororoba.TerminalChannelSeparation.
Locate Library TerminalChannelSeparationReal.
Locate Library OpenGororoba.TerminalChannelSeparationReal.

(** The two channel definitions of each pair are convertible. *)
Example rational_channels_agree :
  TerminalChannelSeparation.binary_channel = OpenGororoba.TerminalChannelSeparation.binary_channel.
Proof. reflexivity. Qed.
Example real_channels_agree :
  TerminalChannelSeparationReal.binary_channel = OpenGororoba.TerminalChannelSeparationReal.binary_channel.
Proof. reflexivity. Qed.

Module RationalInstance.
Import TerminalChannelSeparation.
Open Scope Q_scope.

Definition quantum_statement : Prop :=
  ltac:(let statement := type of TerminalChannelSeparation.observed_means_exclude_common_binary_channel
        in exact statement).

(** The positive-margin premise of the open theorem at the observed centers:
    10/8192 + 4 * 21/1000 < 1947/8192. *)
Lemma observed_positive_margin :
  Qabs (replay_first_observed - replay_third_observed) +
    mean_radius + mean_radius + mean_radius + mean_radius <
    Qabs (hardware_first_observed - hardware_third_observed).
Proof. vm_compute. reflexivity. Qed.

Theorem observed_means_exclude_common_binary_channel_from_open : quantum_statement.
Proof.
  unfold quantum_statement.
  intros hardware_first hardware_third replay_first replay_third
    hardware_first_radius hardware_third_radius replay_first_radius replay_third_radius.
  exact (OpenGororoba.TerminalChannelSeparation.separated_centers_exclude_common_binary_channel
    hardware_first hardware_third replay_first replay_third
    hardware_first_observed hardware_third_observed replay_first_observed replay_third_observed
    mean_radius mean_radius mean_radius mean_radius
    hardware_first_radius hardware_third_radius replay_first_radius replay_third_radius
    observed_positive_margin).
Qed.
End RationalInstance.

Module RealInstance.
Import TerminalChannelSeparationReal.
Open Scope R_scope.

Definition quantum_statement : Prop :=
  ltac:(let statement := type of TerminalChannelSeparationReal.observed_means_exclude_common_binary_channel
        in exact statement).

Lemma observed_positive_margin :
  Rabs (replay_first_observed - replay_third_observed) +
    mean_radius + mean_radius + mean_radius + mean_radius <
    Rabs (hardware_first_observed - hardware_third_observed).
Proof.
  unfold replay_first_observed, replay_third_observed,
    hardware_first_observed, hardware_third_observed, mean_radius.
  rewrite (Rabs_right (4067 / 8192 - 4057 / 8192)) by lra.
  rewrite (Rabs_left (2964 / 8192 - 4911 / 8192)) by lra.
  lra.
Qed.

Theorem observed_means_exclude_common_binary_channel_from_open : quantum_statement.
Proof.
  unfold quantum_statement.
  intros hardware_first hardware_third replay_first replay_third
    hardware_first_radius hardware_third_radius replay_first_radius replay_third_radius.
  exact (OpenGororoba.TerminalChannelSeparationReal.separated_centers_exclude_common_binary_channel
    hardware_first hardware_third replay_first replay_third
    hardware_first_observed hardware_third_observed replay_first_observed replay_third_observed
    mean_radius mean_radius mean_radius mean_radius
    hardware_first_radius hardware_third_radius replay_first_radius replay_third_radius
    observed_positive_margin).
Qed.
End RealInstance.

Print RationalInstance.quantum_statement.
Print RealInstance.quantum_statement.
Print Assumptions RationalInstance.observed_means_exclude_common_binary_channel_from_open.
Print Assumptions RealInstance.observed_means_exclude_common_binary_channel_from_open.
