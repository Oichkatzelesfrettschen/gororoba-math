(** Splitting certificates for the solutions of a homogeneous linear system over a commutative ring.

    For a matrix M with [rows] rows and [n] columns over a source ring A, a certificate is a matrix P ([back],
    n by [rows]), a matrix V ([vectors], n by [kernel]), a matrix C ([functionals], [kernel] by n) and a scalar d
    with P M + V C = d I, checked entry by entry over A. Over every commutative ring B that receives a
    homomorphism h from A, a solution x of M x = 0 with coordinates in B then satisfies h(d) x = V (C x): after
    multiplication by h(d), every solution is the combination of the columns of V with coefficients C x.

    Convention: [matrix r j], [back i r], [vectors i t] and [functionals t j] name row then column. Finite sums
    are [dsum] of CdTowerRingBasis.v. [forall_below n test] decides a property of the numbers below n. *)

From Stdlib Require Import Ring Lia PeanoNat List Bool.
Require Import CdTowerRing CdTowerRingBasis CdTowerRingBaseChange MatrixLeftInverseCertificate.

Definition forall_below (n : nat) (test : nat -> bool) : bool := forallb test (seq 0 n).

Lemma forall_below_spec n test : forall_below n test = true -> forall i, (i < n)%nat -> test i = true.
Proof.
  unfold forall_below. intros E i Hi. rewrite forallb_forall in E. apply E. apply in_seq. lia.
Qed.

Module SplittingCertificate (A B : CommutativeRing) (H : RingHom A B).
Module LC := LeftInverseCertificate A B H.
Module SA := LC.SA.
Module SB := LC.SB.

Add Ring splitting_target : B.ring_th.

Section Certificate.

Variables (rows n kernel : nat) (d : A.t) (matrix back vectors functionals : nat -> nat -> A.t).

Hypothesis splitting : forall i j, (i < n)%nat -> (j < n)%nat ->
  A.add (SA.dsum rows (fun r => A.mul (back i r) (matrix r j)))
        (SA.dsum kernel (fun t => A.mul (vectors i t) (functionals t j))) =
  if Nat.eqb j i then d else A.zero.

(** A solution over the target ring: sum_j h(M_rj) x_j = 0 in every row r. *)
Definition solution (x : nat -> B.t) : Prop :=
  forall r, (r < rows)%nat -> SB.dsum n (fun j => B.mul (H.h (matrix r j)) (x j)) = B.zero.

(** The coefficient of the t-th column of V: the t-th row of C applied to x. *)
Definition coefficient (x : nat -> B.t) (t : nat) : B.t :=
  SB.dsum n (fun j => B.mul (H.h (functionals t j)) (x j)).

Theorem solutions_spanned (x : nat -> B.t) : solution x ->
  forall i, (i < n)%nat ->
  B.mul (H.h d) (x i) = SB.dsum kernel (fun t => B.mul (H.h (vectors i t)) (coefficient x t)).
Proof.
  intros S i Hi. unfold solution in S. unfold coefficient.
  assert (E : SB.dsum n (fun j => B.mul (B.mul (H.h d) (x j)) (if Nat.eqb j i then B.one else B.zero)) =
              B.mul (H.h d) (x i)).
  { rewrite SB.dsum_delta, (proj2 (Nat.ltb_lt _ _) Hi). reflexivity. }
  rewrite <- E.
  rewrite (SB.dsum_ext n _
             (fun j => B.add
                (SB.dsum rows (fun r => B.mul (H.h (back i r)) (B.mul (H.h (matrix r j)) (x j))))
                (SB.dsum kernel
                   (fun t => B.mul (H.h (vectors i t)) (B.mul (H.h (functionals t j)) (x j)))))).
  - rewrite LC.dsum_add.
    rewrite (LC.dsum_swap n rows (fun r j => B.mul (H.h (back i r)) (B.mul (H.h (matrix r j)) (x j)))).
    rewrite (LC.dsum_swap n kernel
               (fun t j => B.mul (H.h (vectors i t)) (B.mul (H.h (functionals t j)) (x j)))).
    rewrite (SB.dsum_ext rows _ (fun _ => B.zero)).
    + rewrite SB.dsum_zero.
      rewrite (SB.dsum_ext kernel _
                 (fun t => B.mul (H.h (vectors i t))
                             (SB.dsum n (fun j => B.mul (H.h (functionals t j)) (x j)))))
        by (intros t _; apply LC.dsum_scale_left).
      ring.
    + intros r Hr. rewrite LC.dsum_scale_left, (S r Hr). ring.
  - intros j Hj.
    assert (E2 : B.add (SB.dsum rows (fun r => B.mul (H.h (back i r)) (H.h (matrix r j))))
                       (SB.dsum kernel (fun t => B.mul (H.h (vectors i t)) (H.h (functionals t j)))) =
                 H.h (if Nat.eqb j i then d else A.zero)).
    { rewrite <- (splitting i j Hi Hj), H.h_add, !LC.h_dsum. f_equal; apply SB.dsum_ext; intros m _;
        rewrite H.h_mul; reflexivity. }
    rewrite (SB.dsum_ext rows _ (fun r => B.mul (B.mul (H.h (back i r)) (H.h (matrix r j))) (x j)))
      by (intros; ring).
    rewrite (SB.dsum_ext kernel _
               (fun t => B.mul (B.mul (H.h (vectors i t)) (H.h (functionals t j))) (x j)))
      by (intros; ring).
    rewrite !LC.dsum_scale_right.
    transitivity (B.mul (H.h (if Nat.eqb j i then d else A.zero)) (x j)); [| rewrite <- E2; ring].
    destruct (Nat.eqb j i); [ring | rewrite H.h_zero; ring].
Qed.

End Certificate.

End SplittingCertificate.
