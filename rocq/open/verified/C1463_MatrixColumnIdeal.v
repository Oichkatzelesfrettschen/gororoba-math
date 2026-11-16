(** * C-1463: the column matrices form a minimal left ideal of dimension n.

    Convention: an n x n real matrix is a function [nat -> nat -> R] read on
    the rows and columns 0 .. n - 1; [mat_eq n] equates two matrices that
    agree there, and [mmul n A B] is the row-by-column product, the sum
    running over 0 .. n - 1.  [col_space n j] is the set of matrices whose
    entries outside column j vanish, and [unit_col j i] is the matrix with 1
    at row i, column j and 0 elsewhere.

    The module proves that [col_space n j] is closed under addition and under
    left multiplication by every matrix ([col_space_add],
    [col_space_left_ideal]); that the n matrices [unit_col j i], i < n, lie
    in it, span it and are linearly independent ([unit_col_in_col_space],
    [col_space_span], [col_space_independent]), so its dimension is n; and
    that it is minimal: a nonzero matrix of it generates every matrix of it
    by left multiplication ([col_space_generated]), so a left ideal inside
    it that holds a nonzero matrix holds all of it ([col_space_minimal]).
    [C1463_minimal_left_ideal_dim_16] is the instance n = 16.

    C1463_ArithmeticInventory.minimal_ideal_dim states 256 / 16 = 16 and
    calls it the dimension of the minimal left ideal of Cl(8), which is
    M(16, R).  This module proves the matrix side of that sentence.  The
    isomorphism of a Clifford algebra with M(16, R), and any map from this
    ideal to the sedenions, have no theorem here; that both dimensions equal
    16 is arithmetic. *)

From Stdlib Require Import Reals Lra Lia Arith.

Local Open Scope R_scope.

Definition mat : Type := nat -> nat -> R.

Fixpoint sum_to (n : nat) (f : nat -> R) : R :=
  match n with
  | O => 0
  | S m => sum_to m f + f m
  end.

Definition mmul (n : nat) (A B : mat) : mat :=
  fun i k => sum_to n (fun l => A i l * B l k).

Definition mat_eq (n : nat) (A B : mat) : Prop :=
  forall i k, (i < n)%nat -> (k < n)%nat -> A i k = B i k.

Definition col_space (n j : nat) (M : mat) : Prop :=
  forall i k, (i < n)%nat -> (k < n)%nat -> k <> j -> M i k = 0.

Definition unit_col (j i : nat) : mat :=
  fun r c => if Nat.eqb r i then (if Nat.eqb c j then 1 else 0) else 0.

Lemma sum_to_zero :
  forall n f, (forall l, (l < n)%nat -> f l = 0) -> sum_to n f = 0.
Proof.
  induction n as [|m IH]; intros f Hf; simpl.
  - reflexivity.
  - rewrite IH by (intros l Hl; apply Hf; lia).
    rewrite (Hf m) by lia. ring.
Qed.

Lemma sum_to_single :
  forall n p f, (p < n)%nat ->
    (forall l, (l < n)%nat -> l <> p -> f l = 0) -> sum_to n f = f p.
Proof.
  induction n as [|m IH]; intros p f Hp Hf; simpl.
  - lia.
  - destruct (Nat.eq_dec p m) as [E | E].
    + subst p. rewrite sum_to_zero; [ring |].
      intros l Hl. apply Hf; lia.
    + assert (Hs : sum_to m f = f p).
      { apply IH; [lia |]. intros l Hl Hlp. apply Hf; lia. }
      rewrite Hs, (Hf m) by lia. ring.
Qed.

Theorem col_space_add :
  forall n j M N, col_space n j M -> col_space n j N ->
    col_space n j (fun r c => M r c + N r c).
Proof.
  intros n j M N HM HN i k Hi Hk Hkj.
  rewrite (HM i k Hi Hk Hkj), (HN i k Hi Hk Hkj). ring.
Qed.

Theorem col_space_left_ideal :
  forall n j A M, col_space n j M -> col_space n j (mmul n A M).
Proof.
  intros n j A M HM i k Hi Hk Hkj. unfold mmul. cbv beta.
  apply sum_to_zero. intros l Hl. cbv beta.
  rewrite (HM l k Hl Hk Hkj). ring.
Qed.

Theorem unit_col_in_col_space : forall n j i, col_space n j (unit_col j i).
Proof.
  intros n j i r c Hr Hc Hcj. cbv beta delta [unit_col].
  destruct (Nat.eqb r i); [| reflexivity].
  destruct (Nat.eqb_spec c j) as [E | E]; [contradiction | reflexivity].
Qed.

Theorem col_space_span :
  forall n j M, col_space n j M ->
    mat_eq n M (fun r c => sum_to n (fun i => M i j * unit_col j i r c)).
Proof.
  intros n j M HM r c Hr Hc. cbv beta.
  rewrite (sum_to_single n r); [| exact Hr |].
  - cbv beta delta [unit_col]. rewrite Nat.eqb_refl.
    destruct (Nat.eqb_spec c j) as [E | E]; cbv beta iota.
    + subst c. ring.
    + rewrite (HM r c Hr Hc E). ring.
  - intros l Hl Hlr. cbv beta delta [unit_col].
    destruct (Nat.eqb_spec r l) as [E | E]; cbv beta iota; [exfalso; lia | ring].
Qed.

Theorem col_space_independent :
  forall n j (a : nat -> R), (j < n)%nat ->
    mat_eq n (fun r c => sum_to n (fun i => a i * unit_col j i r c))
             (fun _ _ => 0) ->
    forall i, (i < n)%nat -> a i = 0.
Proof.
  intros n j a Hj H i Hi.
  specialize (H i j Hi Hj). cbv beta in H.
  rewrite (sum_to_single n i) in H; [| exact Hi |].
  - cbv beta delta [unit_col] in H. rewrite !Nat.eqb_refl in H.
    cbv beta iota in H. lra.
  - intros l Hl Hli. cbv beta delta [unit_col].
    destruct (Nat.eqb_spec i l) as [E | E]; cbv beta iota; [exfalso; lia | ring].
Qed.

(** The left factor that moves row p of M onto every row: row i of the
    product is N i j / M p j times row p of M. *)
Definition row_mover (N M : mat) (j p : nat) : mat :=
  fun i l => if Nat.eqb l p then N i j / M p j else 0.

Theorem col_space_generated :
  forall n j M N p, (p < n)%nat -> col_space n j M -> col_space n j N ->
    M p j <> 0 -> mat_eq n (mmul n (row_mover N M j p) M) N.
Proof.
  intros n j M N p Hp HM HN HMp i k Hi Hk. unfold mmul. cbv beta.
  rewrite (sum_to_single n p); [| exact Hp |].
  - cbv beta delta [row_mover]. rewrite Nat.eqb_refl. cbv beta iota.
    destruct (Nat.eq_dec k j) as [E | E].
    + subst k. field. exact HMp.
    + rewrite (HM p k Hp Hk E), (HN i k Hi Hk E). ring.
  - intros l Hl Hlp. cbv beta delta [row_mover].
    destruct (Nat.eqb_spec l p) as [E | E]; cbv beta iota; [contradiction | ring].
Qed.

(** A set I of n x n matrices (closed under [mat_eq n]) that is closed
    under left multiplication, lies in column j and holds a nonzero matrix
    holds every matrix of column j. *)
Theorem col_space_minimal :
  forall n j (I : mat -> Prop),
    (forall M N, mat_eq n M N -> I M -> I N) ->
    (forall A M, I M -> I (mmul n A M)) ->
    (forall M, I M -> col_space n j M) ->
    (exists M p k, I M /\ (p < n)%nat /\ (k < n)%nat /\ M p k <> 0) ->
    forall N, col_space n j N -> I N.
Proof.
  intros n j I Hresp Hmul Hcol [M [p [k [HI [Hp [Hk HMpk]]]]]] N HN.
  destruct (Nat.eq_dec k j) as [E | E].
  - subst k.
    apply (Hresp (mmul n (row_mover N M j p) M) N).
    + exact (col_space_generated n j M N p Hp (Hcol M HI) HN HMpk).
    + apply Hmul. exact HI.
  - exfalso. apply HMpk. exact (Hcol M HI p k Hp Hk E).
Qed.

Theorem C1463_minimal_left_ideal_dim_16 :
  (forall A M, col_space 16 0 M -> col_space 16 0 (mmul 16 A M)) /\
  (forall i, col_space 16 0 (unit_col 0 i)) /\
  (forall M, col_space 16 0 M ->
     mat_eq 16 M (fun r c => sum_to 16 (fun i => M i 0%nat * unit_col 0 i r c))) /\
  (forall a : nat -> R,
     mat_eq 16 (fun r c => sum_to 16 (fun i => a i * unit_col 0 i r c))
               (fun _ _ => 0) ->
     forall i, (i < 16)%nat -> a i = 0) /\
  (forall I : mat -> Prop,
     (forall M N, mat_eq 16 M N -> I M -> I N) ->
     (forall A M, I M -> I (mmul 16 A M)) ->
     (forall M, I M -> col_space 16 0 M) ->
     (exists M p k, I M /\ (p < 16)%nat /\ (k < 16)%nat /\ M p k <> 0) ->
     forall N, col_space 16 0 N -> I N).
Proof.
  split; [| split; [| split; [| split]]].
  - intros A M. apply col_space_left_ideal.
  - intros i. apply unit_col_in_col_space.
  - intros M. apply col_space_span.
  - intros a. apply col_space_independent. lia.
  - intros I. apply col_space_minimal.
Qed.
