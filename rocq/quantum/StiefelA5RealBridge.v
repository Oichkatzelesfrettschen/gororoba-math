(** Bridge of the Lean theorem `CayleyDickson.Tower.stiefel_zero_divisor_real` of
    lean/GororobaMath/CayleyDickson/StiefelRealZeroDivisor.lean: over the real numbers a Stiefel element of the
    level-5 tower is a zero divisor. The Lean theorem is the complexification of `CayleyDickson.Tower.stiefel_zero_divisor`
    of lean/GororobaMath/CayleyDickson/StiefelZeroDivisor.lean followed by the descent of the annihilator to its
    real and imaginary parts, which the Rocq source StiefelA5Real.v proves for `real_stiefel_zero_divisor`.

    Convention: RT.cd 5 of CdTowerRing.v is Lean's `Tower ℝ 5`, with the product (a, b)(c, d) = (ac - conj(d) b,
    da + b conj(c)) and the identity as the conjugation of the coefficients; RT.mul 5 is Lean's `*` and RT.zero 5 is `0`.

    Substituted values: the pure halves `p`, `q` of Lean's `Tower ℝ 4` are `rmk 4 (fun j => if j = 0 then 0 else a j)`
    and the same with `b`, so that `re 4 p = 0` and `re 4 q = 0` hold by construction and `mk p q` is `ry5 a b`.
    The Lean sum `dot 4 p p` over the 16 coordinates reduces to the sum over the 15 nonzero indices (the Lean lemma
    `Tower.dot_four_eq`), which is `rsum 15 (fun m => a (S m) * a (S m))`; likewise `dot 4 q q` and `dot 4 p q`.
    The hypotheses `dot 4 p p = dot 4 q q` and `dot 4 p q = 0` become the two hypotheses below, and the conclusion
    `exists x, x <> 0 /\ mk p q * x = 0` is the conclusion below.

    The Rocq statement is narrower than the Lean one: it takes the coordinates of `p` and `q` as real sequences
    `a`, `b` with the index 0 dropped, where Lean takes elements of `Tower ℝ 4` with `re 4 p = 0`; the two
    parametrizations of the pure elements agree. *)

From Stdlib Require Import Reals.
Require Import StiefelA5Real.
Local Open Scope R_scope.

Theorem stiefel_zero_divisor_real_bridge (a b : nat -> R) :
  rsum 15 (fun m => a (S m) * a (S m)) = rsum 15 (fun m => b (S m) * b (S m)) ->
  rsum 15 (fun m => a (S m) * b (S m)) = 0 ->
  exists x : RT.cd 5, x <> RT.zero 5 /\ RT.mul 5 (ry5 a b) x = RT.zero 5.
Proof. exact (real_stiefel_zero_divisor a b). Qed.
