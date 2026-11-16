(** * C-1138: the Wick damping factor decreases on [0, pi/2] and is minimal at pi/2.

    Convention: the damping factor of the topological friction at the Wick
    angle theta with friction scale H is exp (- H * sin theta), the ratio
    F(theta) / F(0) of the friction at the angle to the friction at zero.
    The module defines no friction function F, so H is a real parameter and
    the module relates the factor to no associator norm or quantized gap.

    The module proves, for H >= 0 and the Stdlib sine:
    - the factor is non-increasing in theta on [0, pi/2]; the ordering of
      the sines follows from sin_incr_1, so no hypothesis on sin theta1 and
      sin theta2 remains;
    - the factor at pi/2 is exp (- H), without a hypothesis on sin (PI / 2);
    - the factor at pi/2 is a lower bound of the factor at every angle. *)

From Stdlib Require Import Reals Lra.
From OpenGororoba Require Import Prelude.

Open Scope R_scope.

Definition wick_damping (H theta : R) : R := exp (- H * sin theta).

Lemma exp_monotone : forall a b : R, a <= b -> exp a <= exp b.
Proof.
  intros a b Hab.
  destruct (Rle_lt_or_eq_dec a b Hab) as [Hlt | Heq].
  - apply Rlt_le. apply exp_increasing. exact Hlt.
  - rewrite Heq. apply Rle_refl.
Qed.

Theorem wick_damping_decreasing_on_quarter_turn :
  forall H theta1 theta2 : R,
    H >= 0 -> 0 <= theta1 -> theta1 <= theta2 -> theta2 <= PI / 2 ->
    wick_damping H theta2 <= wick_damping H theta1.
Proof.
  intros H theta1 theta2 HH H1 H12 H2. unfold wick_damping.
  pose proof PI_RGT_0 as Hpi.
  assert (Hs : sin theta1 <= sin theta2).
  { apply sin_incr_1; lra. }
  apply exp_monotone. nra.
Qed.

Theorem wick_damping_at_quarter_turn :
  forall H : R, wick_damping H (PI / 2) = exp (- H).
Proof.
  intro H. unfold wick_damping. rewrite sin_PI2.
  replace (- H * 1) with (- H) by ring. reflexivity.
Qed.

Theorem wick_damping_minimal_at_quarter_turn :
  forall H theta : R,
    H >= 0 -> wick_damping H (PI / 2) <= wick_damping H theta.
Proof.
  intros H theta HH. unfold wick_damping. rewrite sin_PI2.
  pose proof (SIN_bound theta) as [_ Hs].
  apply exp_monotone. nra.
Qed.
