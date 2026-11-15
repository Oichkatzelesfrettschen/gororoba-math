(** * C-1233: Total Chern number = 0 under time-reversal symmetry.

    The module proves that if the Berry curvature F satisfies has_trs F
    (F kx ky = - F (-kx) (-ky)), then chern_integral F = 0.

    The result rests on two axioms of TightBindingTopology:
    chern_splits_into_valleys (the full integral is the sum of the K and K'
    valley integrals) and trs_swaps_valleys (under has_trs the K' integral
    is the negative of the K integral).  The statement is relative to these
    axioms, to the parameters chern_integral, valley_integral_K and
    valley_integral_Kp, and to the real-number axioms of the standard
    library; the linearity axiom chern_integral_linear is unused.

    Convention: berry_curvature is R -> R -> R, and chern_integral is a
    real-valued functional of it.

    The proof splits the integral into valleys, replaces the K' valley by
    the negated K valley, and cancels in the reals. *)

From OpenGororoba Require Import Prelude.
Require Import OpenGororoba.TightBindingTopology.

Open Scope R_scope.

Theorem chern_integral_zero_under_trs :
  forall F : berry_curvature, has_trs F -> chern_integral F = 0.
Proof.
  intros F Htrs.
  rewrite (chern_splits_into_valleys F), (trs_swaps_valleys F Htrs).
  lra.
Qed.
