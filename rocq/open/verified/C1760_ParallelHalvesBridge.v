(** * The vector e_1 + e_9 of C-1760 is the parallel-halves vector.

    The equal-norm theorem koebisu_e1_e9 of C1465_KoebisuEqualNorm.v names the
    vector as sed_add (sed_e 1) (sed_e 9), and the trivial-kernel theorem
    parallel_halves_trivial_kernel of SedenionMembershipConstraints.v names it
    as parallel_imaginary_halves = mkSed (oct_e 1) (oct_e 1). Convention: the
    sedenion index i < 8 is the basis vector of the low octonion half, and
    index 8 + i the one of the high half. The two vectors agree coordinate by
    coordinate, so the left kernel of the vector of C-1760 is trivial. *)

From Stdlib Require Import Reals Lra.
From OpenGororoba Require Import Prelude CayleyDicksonAlgebra Sedenion OctonionNorm
  SedenionMembershipConstraints.
From OpenGororobaVerified Require Import C1465_KoebisuEqualNorm.
Open Scope R_scope.

Theorem koebisu_e1_e9_is_parallel_halves :
  sed_add (sed_e 1%nat) (sed_e 9%nat) = parallel_imaginary_halves.
Proof.
  cbv [parallel_imaginary_halves sed_add sed_e sed_zero oct_add oct_e oct_zero
       quat_add quat_zero quat_one sed_lo sed_hi oct_lo oct_hi qa qb qc qd].
  f_equal; f_equal; f_equal; ring.
Qed.
Print Assumptions koebisu_e1_e9_is_parallel_halves.

Theorem koebisu_e1_e9_trivial_kernel : forall value,
  sed_mul (sed_add (sed_e 1%nat) (sed_e 9%nat)) value = sed_zero -> value = sed_zero.
Proof.
  intros value H.
  rewrite koebisu_e1_e9_is_parallel_halves in H.
  exact (parallel_halves_trivial_kernel value H).
Qed.
Print Assumptions koebisu_e1_e9_trivial_kernel.

Theorem koebisu_e1_e9_equal_norms_and_trivial_kernel :
  sed_norm_diff (sed_add (sed_e 1%nat) (sed_e 9%nat)) = 0
  /\ (forall value,
        sed_mul (sed_add (sed_e 1%nat) (sed_e 9%nat)) value = sed_zero ->
        value = sed_zero).
Proof.
  exact (conj koebisu_e1_e9 koebisu_e1_e9_trivial_kernel).
Qed.
