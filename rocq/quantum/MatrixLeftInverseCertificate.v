(** Left-inverse certificates of independent columns over a commutative ring.

    For a matrix M with [rows] rows and [columns] columns over a source ring A, a certificate is a matrix L with
    [columns] rows and [rows] columns and a scalar d with L M = d I, checked entry by entry over A. Over every
    commutative ring B that receives a homomorphism h from A, a column relation M a = 0 with coefficients a_j
    in B then has h(d) a_l = 0 for every l: the image of the relation under L is h(d) a. Where h(d) is a nonzero
    divisor of B the columns of M are linearly independent over B, so M has rank [columns] where B is a field.

    Convention: [matrix r j] is the entry of row r and column j, [left l r] the entry of row l and column r,
    [entry table r j] reads row r, column j of a list of rows, and [sparse_entry table l r] reads row l of a
    list of rows that hold their nonzero entries as pairs (column, value), with zero for an absent column.
    Both readers are total: a missing row, column or key reads as zero, and the first of two entries with one
    key wins. [dense_shape table rows columns] and [sparse_shape table lines bound] decide that a table has
    exactly the stated shape (every row of the stated length; every key below the bound and no key twice in a
    line), so that a certificate which checks them rests on no default. Finite sums are [dsum] of
    CdTowerRingBasis.v. *)

From Stdlib Require Import Ring Lia PeanoNat List Bool.
Require Import CdTowerRing CdTowerRingBasis CdTowerRingBaseChange.

Module LeftInverseCertificate (A B : CommutativeRing) (H : RingHom A B).
Module SA := RingTowerBasis A.
Module SB := RingTowerBasis B.

Add Ring left_inverse_target : B.ring_th.

Definition entry (table : list (list A.t)) (r j : nat) : A.t := nth j (nth r table nil) A.zero.

Definition sparse_entry (table : list (list (nat * A.t))) (l r : nat) : A.t :=
  match find (fun item => Nat.eqb (fst item) r) (nth l table nil) with
  | Some item => snd item
  | None => A.zero
  end.

Definition dense_shape {X : Type} (table : list (list X)) (rows columns : nat) : bool :=
  Nat.eqb (length table) rows && forallb (fun row => Nat.eqb (length row) columns) table.

Fixpoint distinct_keys {X : Type} (line : list (nat * X)) : bool :=
  match line with
  | nil => true
  | item :: rest => negb (existsb (fun other => Nat.eqb (fst other) (fst item)) rest) && distinct_keys rest
  end.

Definition sparse_shape {X : Type} (table : list (list (nat * X))) (lines bound : nat) : bool :=
  Nat.eqb (length table) lines &&
  forallb (fun line => forallb (fun item => Nat.ltb (fst item) bound) line && distinct_keys line) table.

Lemma h_dsum n g : H.h (SA.dsum n g) = SB.dsum n (fun m => H.h (g m)).
Proof.
  induction n as [|m IH]; cbn [SA.dsum SB.dsum]; [apply H.h_zero | rewrite H.h_add, IH; reflexivity].
Qed.

Lemma dsum_add n g g' : SB.dsum n (fun m => B.add (g m) (g' m)) = B.add (SB.dsum n g) (SB.dsum n g').
Proof. induction n as [|m IH]; cbn [SB.dsum]; [ring | rewrite IH; ring]. Qed.

Lemma dsum_scale_left n r g : SB.dsum n (fun m => B.mul r (g m)) = B.mul r (SB.dsum n g).
Proof. induction n as [|m IH]; cbn [SB.dsum]; [ring | rewrite IH; ring]. Qed.

Lemma dsum_scale_right n r g : SB.dsum n (fun m => B.mul (g m) r) = B.mul (SB.dsum n g) r.
Proof. induction n as [|m IH]; cbn [SB.dsum]; [ring | rewrite IH; ring]. Qed.

Lemma dsum_swap n m (f : nat -> nat -> B.t) :
  SB.dsum n (fun j => SB.dsum m (fun r => f r j)) = SB.dsum m (fun r => SB.dsum n (fun j => f r j)).
Proof.
  induction m as [|p IH]; cbn [SB.dsum]; [apply SB.dsum_zero | rewrite dsum_add, IH; reflexivity].
Qed.

Section Certificate.

Variables (rows columns : nat) (d : A.t) (matrix left : nat -> nat -> A.t).

Hypothesis left_inverse : forall l j, (l < columns)%nat -> (j < columns)%nat ->
  SA.dsum rows (fun r => A.mul (left l r) (matrix r j)) = if Nat.eqb j l then d else A.zero.

(** A column relation over the target ring: sum_j h(M_rj) a_j = 0 in every row r. *)
Definition relation (a : nat -> B.t) : Prop :=
  forall r, (r < rows)%nat -> SB.dsum columns (fun j => B.mul (H.h (matrix r j)) (a j)) = B.zero.

Theorem relation_coefficients (a : nat -> B.t) :
  relation a -> forall l, (l < columns)%nat -> B.mul (H.h d) (a l) = B.zero.
Proof.
  intros R l Hl. unfold relation in R.
  assert (E : SB.dsum columns
                (fun j => B.mul (B.mul (H.h d) (a j)) (if Nat.eqb j l then B.one else B.zero)) =
              B.mul (H.h d) (a l)).
  { rewrite SB.dsum_delta, (proj2 (Nat.ltb_lt _ _) Hl). reflexivity. }
  rewrite <- E.
  rewrite (SB.dsum_ext columns _
             (fun j => SB.dsum rows (fun r => B.mul (H.h (left l r)) (B.mul (H.h (matrix r j)) (a j))))).
  - rewrite dsum_swap.
    rewrite (SB.dsum_ext rows _ (fun _ => B.zero)); [apply SB.dsum_zero |].
    intros r Hr. rewrite dsum_scale_left, (R r Hr). ring.
  - intros j Hj.
    assert (E2 : SB.dsum rows (fun r => B.mul (H.h (left l r)) (H.h (matrix r j))) =
                 H.h (if Nat.eqb j l then d else A.zero)).
    { rewrite <- (left_inverse l j Hl Hj), h_dsum. apply SB.dsum_ext. intros r _. rewrite H.h_mul. reflexivity. }
    rewrite (SB.dsum_ext rows _ (fun r => B.mul (B.mul (H.h (left l r)) (H.h (matrix r j))) (a j)))
      by (intros; ring).
    rewrite dsum_scale_right, E2.
    destruct (Nat.eqb j l); [ring | rewrite H.h_zero; ring].
Qed.

(** Where h(d) is a nonzero divisor, the only column relation is the zero relation. *)
Theorem columns_independent (a : nat -> B.t) :
  (forall x, B.mul (H.h d) x = B.zero -> x = B.zero) ->
  relation a -> forall l, (l < columns)%nat -> a l = B.zero.
Proof. intros regular R l Hl. apply regular. exact (relation_coefficients a R l Hl). Qed.

(** An inverse of h(d) makes h(d) a nonzero divisor. *)
Theorem columns_independent_invertible (inverse : B.t) (a : nat -> B.t) :
  B.mul inverse (H.h d) = B.one ->
  relation a -> forall l, (l < columns)%nat -> a l = B.zero.
Proof.
  intros inverse_law. apply columns_independent. intros x E.
  transitivity (B.mul (B.mul inverse (H.h d)) x); [rewrite inverse_law; ring |].
  transitivity (B.mul inverse (B.mul (H.h d) x)); [ring | rewrite E; ring].
Qed.

End Certificate.

End LeftInverseCertificate.
