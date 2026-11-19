(** * C-874: the axial taper and the shape function at the bubble
    center, stated for the model functions.

    Successor of C874_YorkTimeVanishesInterior.v, whose bytes a retained
    record of gororoba-open pins by sha256.  The theorems here are the
    theorems of that file under new names; this header corrects two
    statements of the original header.

    Convention: [axial_taper], [axial_taper_deriv] and [shape_fun] are the
    model functions of OpenGororoba.WarpShapeFunction; x, L, sigma_x, r_s,
    R and sigma are real numbers with the positivity hypotheses each
    theorem names.

    [C874_model_axial_deriv_zero]: the derivative of the axial taper
    vanishes at x = 0.  [C874_model_axial_taper_unity]: the axial taper is
    1 at x = 0.  [C874_model_shape_unity]: the shape function is 1 at
    r_s = 0.

    Scope: the theorems concern these model functions only.  They are the
    ingredients the original header combines into a vanishing York time
    theta = div(beta) at the center; that combination, and any statement
    about the divergence of the shift of the implemented metric, is not
    proved here.

    Corresponding tests in crates/gr_core/src/warp_metric.rs of
    gororoba-open (commit 957fc28f): test_axial_taper_center and
    test_shape_function_at_center assert the values these theorems state;
    test_york_time_zero_at_center asserts |theta| < 0.1 for the default
    parameters.  The original header names test_york_time_center_zero,
    which names no test. *)

From Stdlib Require Import Rtrigo_def.
From OpenGororoba Require Import Prelude Tanh WarpShapeFunction.

Open Scope R_scope.

Theorem C874_model_axial_deriv_zero : forall L sigma_x : R,
  sigma_x > 0 -> L > 0 ->
  axial_taper_deriv 0 L sigma_x = 0.
Proof.
  exact axial_taper_deriv_zero.
Qed.

Theorem C874_model_axial_taper_unity : forall L sigma_x : R,
  sigma_x > 0 -> L > 0 ->
  axial_taper 0 L sigma_x = 1.
Proof.
  exact axial_taper_center.
Qed.

Theorem C874_model_shape_unity : forall Rb sig : R,
  sig > 0 -> Rb > 0 ->
  shape_fun 0 Rb sig = 1.
Proof.
  exact shape_fun_center.
Qed.
