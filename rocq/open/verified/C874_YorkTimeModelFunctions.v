(** * C-874: the axial taper and the shape function at the bubble
    center, stated for the model functions.

    Successor of C874_YorkTimeVanishesInterior.v, whose bytes a retained
    record of gororoba-open pins by sha256.  The theorems here are the
    theorems of that file under new names; this header corrects two
    statements of the original header.

    Convention: [axial_taper], [axial_taper_deriv] and [shape_fun] are the
    model functions of OpenGororoba.WarpShapeFunction.  Each theorem
    evaluates the first argument (the axial coordinate x, or the radius
    r_s) at 0 and quantifies over the remaining real parameters: L and
    sigma_x with sigma_x > 0 and L > 0; Rb and sig with sig > 0 and
    Rb > 0.

    [C874_model_axial_deriv_zero]: the derivative of the axial taper
    vanishes at x = 0.  [C874_model_axial_taper_unity]: the axial taper is
    1 at x = 0.  [C874_model_shape_unity]: the shape function is 1 at
    r_s = 0.

    Scope: the theorems concern these model functions only.  They are the
    ingredients the original header combines into a vanishing York time
    theta = div(beta) at the center; that combination, and any statement
    about the divergence of the shift of the implemented metric, is not
    proved here.

    Numerical tests in crates/gr_core/src/warp_metric.rs of gororoba-open
    (commit 957fc28f), each at fixed parameters in f64 and none an
    instance of a theorem here: test_axial_taper_center and
    test_shape_function_at_center assert values within 0.01 of 1 at 0;
    test_york_time_zero_at_center asserts |theta| < 0.1 at the origin for
    the default parameters, the York time statement this file does not
    prove.  The original header names test_york_time_center_zero, which
    names no test. *)

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
