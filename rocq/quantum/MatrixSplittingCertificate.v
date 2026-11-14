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
Add Ring splitting_source : A.ring_th.

(** [line_entry line r] is the value of key r in one line of a sparse table, zero for an absent key;
    [sparse_sum line g] is the sum of value * g(key) over the items of the line. For a line with distinct
    keys below [rows], [dsum_sparse] equates it with the dense sum over the keys below [rows]. *)
Definition line_entry (line : list (nat * A.t)) (r : nat) : A.t :=
  match find (fun item => Nat.eqb (fst item) r) line with
  | Some item => snd item
  | None => A.zero
  end.

Definition sparse_sum (line : list (nat * A.t)) (g : nat -> A.t) : A.t :=
  fold_right (fun item acc => A.add (A.mul (snd item) (g (fst item))) acc) A.zero line.

Lemma line_entry_cons k v rest r :
  line_entry ((k, v) :: rest) r = if Nat.eqb k r then v else line_entry rest r.
Proof. unfold line_entry. cbn [find fst]. destruct (Nat.eqb k r); reflexivity. Qed.

Lemma line_entry_absent line k :
  existsb (fun other => Nat.eqb (fst other) k) line = false -> line_entry line k = A.zero.
Proof.
  induction line as [|[k' v] rest IH]; [reflexivity |]. cbn [existsb fst]. intro E.
  apply orb_false_elim in E as [E1 E2]. rewrite line_entry_cons, E1. exact (IH E2).
Qed.

Lemma dsum_add_source n g g' : SA.dsum n (fun m => A.add (g m) (g' m)) = A.add (SA.dsum n g) (SA.dsum n g').
Proof. induction n as [|m IH]; cbn [SA.dsum]; [ring | rewrite IH; ring]. Qed.

Lemma dsum_sparse rows line g :
  forallb (fun item => Nat.ltb (fst item) rows) line = true -> LC.distinct_keys line = true ->
  SA.dsum rows (fun r => A.mul (line_entry line r) (g r)) = sparse_sum line g.
Proof.
  induction line as [|[k v] rest IH].
  - intros _ _. cbn [sparse_sum fold_right]. rewrite (SA.dsum_ext rows _ (fun _ => A.zero)).
    + apply SA.dsum_zero.
    + intros r _. unfold line_entry. cbn [find]. ring.
  - cbn [forallb LC.distinct_keys sparse_sum fold_right fst snd]. intros R K.
    apply andb_prop in R as [Rk Rrest]. apply andb_prop in K as [Kk Krest].
    apply negb_true_iff in Kk. fold (sparse_sum rest g). rewrite <- (IH Rrest Krest).
    rewrite (SA.dsum_ext rows _
               (fun r => A.add (A.mul (A.mul v (g r)) (if Nat.eqb r k then A.one else A.zero))
                               (A.mul (line_entry rest r) (g r)))).
    + rewrite dsum_add_source, SA.dsum_delta, Rk. reflexivity.
    + intros r _. rewrite line_entry_cons.
      destruct (Nat.eqb_spec k r) as [->|N].
      * rewrite Nat.eqb_refl, (line_entry_absent rest r Kk). ring.
      * destruct (Nat.eqb_spec r k) as [->|_]; [contradiction | ring].
Qed.

Lemma sparse_shape_line (table : list (list (nat * A.t))) lines bound i :
  LC.sparse_shape table lines bound = true ->
  forallb (fun item => Nat.ltb (fst item) bound) (nth i table nil) = true /\
  LC.distinct_keys (nth i table nil) = true.
Proof.
  unfold LC.sparse_shape. intro S. apply andb_prop in S as [_ S]. rewrite forallb_forall in S.
  destruct (Nat.lt_ge_cases i (length table)) as [L|L].
  - apply andb_prop. apply S. apply nth_In. exact L.
  - rewrite (nth_overflow _ _ L). split; reflexivity.
Qed.

(** The dense sum against line i of a well-formed sparse table is the sparse sum of that line. *)
Lemma dsum_sparse_table (table : list (list (nat * A.t))) lines rows i g :
  LC.sparse_shape table lines rows = true ->
  SA.dsum rows (fun r => A.mul (LC.sparse_entry table i r) (g r)) = sparse_sum (nth i table nil) g.
Proof.
  intro S. destruct (sparse_shape_line table lines rows i S) as [R K]. exact (dsum_sparse rows _ g R K).
Qed.

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
