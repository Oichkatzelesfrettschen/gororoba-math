(** * C-869: the shape-function derivative and the gating function at the
    bubble center, stated for the model functions.

    Successor of C869_InteriorFlat.v, whose bytes a retained record of
    gororoba-open pins by sha256.  The theorems here are the theorems of
    that file under new names; this header corrects two statements of the
    original header.

    Convention: [shape_fun_deriv] and [gating] are the model functions of
    OpenGororoba.WarpShapeFunction.  Each theorem evaluates the first
    argument (the radius r_s, or the cylindrical radius rho) at 0 and
    quantifies over the remaining real parameters: Rb and sig with
    sig > 0 and Rb > 0; rho_0, kappa and delta with kappa > 0, rho_0 > 0
    and delta < rho_0.

    [C869_model_shape_deriv_center_zero]: the derivative of the shape
    function vanishes at r_s = 0, since sech^2 is even.
    [C869_model_gating_interior]: at rho = 0 the gating function is below
    1/2 when delta < rho_0.

    Scope: the theorems concern these model functions only.  No statement
    here is about the extrinsic curvature K_ij of the implemented metric;
    the original header's "K_ij = 0 at the bubble center" is not proved.

    Numerical tests in crates/gr_core/src/warp_metric.rs of gororoba-open
    (commit 957fc28f), each at fixed parameters in f64 and none an
    instance of a theorem here: test_shape_derivative_zero_at_center
    asserts |df/dr(0)| < 0.01; test_gating_interior_is_zero evaluates the
    gating function at rho = 0.1, not 0, and asserts a value below 0.01;
    test_center_extrinsic_curvature_is_zero asserts K_ij = 0 at the origin
    for the default parameters, the statement this file does not prove.
    The original header names test_york_time_center_zero, which names no
    test. *)

From Stdlib Require Import Rtrigo_def.
From OpenGororoba Require Import Prelude Tanh WarpShapeFunction.

Open Scope R_scope.

Theorem C869_model_shape_deriv_center_zero : forall Rb sig : R,
  sig > 0 -> Rb > 0 ->
  shape_fun_deriv 0 Rb sig = 0.
Proof.
  exact shape_fun_deriv_zero.
Qed.

Theorem C869_model_gating_interior : forall rho_0 kappa delta : R,
  kappa > 0 -> rho_0 > 0 -> delta < rho_0 ->
  gating 0 rho_0 kappa delta < 1/2.
Proof.
  exact gating_interior_bound.
Qed.
