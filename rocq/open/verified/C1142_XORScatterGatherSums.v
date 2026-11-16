(** * C-1142: scatter and gather sums over the XOR index map.

    Convention: n = 2^m is the dimension of a Cayley-Dickson algebra and the
    indices are 0 .. n-1.  A term f i j is a function of the source index i and
    the column index j with values in Z.  The scatter sum at the target k adds
    f i j over the pairs (i, j) with i xor j = k, taken over all i and j below
    n; the gather sum at k adds f (k xor j) j over j below n.  The module
    defines no Cayley-Dickson product: f is any term function, so the sums
    stand for the scatter and gather accumulations of the product when f i j is
    the signed product term of e_i and e_j.

    The module proves, for k < 2^m:
    - XOR with a fixed i maps [0, 2^m) bijectively onto itself, which is the
      absence of write collisions;
    - the pairs of the scatter traversal and the pairs of the gather
      traversal are the same set;
    - the scatter sum equals the gather sum for every term function f. *)

From Stdlib Require Import List ZArith Arith PeanoNat Lia Bool.
Import ListNotations.

Open Scope Z_scope.

(** * XOR on the index range. *)

Lemma lxor_below_pow2 : forall a b m : nat,
  (a < 2 ^ m)%nat -> (b < 2 ^ m)%nat -> (Nat.lxor a b < 2 ^ m)%nat.
Proof.
  intros a b m Ha Hb.
  assert (Hpos : (0 < 2 ^ m)%nat) by (apply Nat.neq_0_lt_0; apply Nat.pow_nonzero; discriminate).
  destruct (Nat.eq_dec a 0) as [-> | Ha0]; [rewrite Nat.lxor_0_l; exact Hb |].
  destruct (Nat.eq_dec b 0) as [-> | Hb0]; [rewrite Nat.lxor_0_r; exact Ha |].
  destruct (Nat.eq_dec (Nat.lxor a b) 0) as [H0 | H0]; [rewrite H0; exact Hpos |].
  apply Nat.log2_lt_pow2; [lia |].
  pose proof (Nat.log2_lxor a b) as Hl.
  pose proof (proj1 (Nat.log2_lt_pow2 a m ltac:(lia)) Ha) as H1.
  pose proof (proj1 (Nat.log2_lt_pow2 b m ltac:(lia)) Hb) as H2.
  lia.
Qed.

Lemma lxor_solve : forall i j k : nat,
  Nat.lxor i j = k <-> i = Nat.lxor k j.
Proof.
  intros i j k. split; intro H.
  - rewrite <- H. rewrite Nat.lxor_assoc, Nat.lxor_nilpotent, Nat.lxor_0_r. reflexivity.
  - rewrite H. rewrite Nat.lxor_assoc, Nat.lxor_nilpotent, Nat.lxor_0_r. reflexivity.
Qed.

Theorem xor_map_bijective_on_range : forall i k m : nat,
  (i < 2 ^ m)%nat -> (k < 2 ^ m)%nat ->
  exists j : nat, (j < 2 ^ m)%nat /\ Nat.lxor i j = k /\
    forall j' : nat, (j' < 2 ^ m)%nat -> Nat.lxor i j' = k -> j' = j.
Proof.
  intros i k m Hi Hk.
  exists (Nat.lxor i k). split; [apply lxor_below_pow2; assumption |]. split.
  - rewrite <- Nat.lxor_assoc, Nat.lxor_nilpotent, Nat.lxor_0_l. reflexivity.
  - intros j' _ Hj'. rewrite <- Hj'.
    rewrite <- Nat.lxor_assoc, Nat.lxor_nilpotent, Nat.lxor_0_l. reflexivity.
Qed.

(** * The same pairs. *)

Definition scatter_pair (n k i j : nat) : Prop :=
  (i < n)%nat /\ (j < n)%nat /\ Nat.lxor i j = k.

Definition gather_pair (n k i j : nat) : Prop :=
  (j < n)%nat /\ i = Nat.lxor k j.

Theorem scatter_gather_same_pairs : forall m k i j : nat,
  (k < 2 ^ m)%nat ->
  scatter_pair (2 ^ m) k i j <-> gather_pair (2 ^ m) k i j.
Proof.
  intros m k i j Hk. unfold scatter_pair, gather_pair. split.
  - intros [_ [Hj Hx]]. split; [exact Hj |]. apply lxor_solve. exact Hx.
  - intros [Hj Hi]. split; [| split; [exact Hj |]].
    + rewrite Hi. apply lxor_below_pow2; assumption.
    + apply lxor_solve. exact Hi.
Qed.

(** * The same sums. *)

Definition big_sum (l : list nat) (g : nat -> Z) : Z :=
  fold_right (fun x acc => g x + acc) 0 l.

Lemma big_sum_nil : forall g : nat -> Z, big_sum [] g = 0.
Proof. reflexivity. Qed.

Lemma big_sum_cons : forall (a : nat) (l : list nat) (g : nat -> Z),
  big_sum (a :: l) g = g a + big_sum l g.
Proof. reflexivity. Qed.

Lemma big_sum_zero : forall l : list nat, big_sum l (fun _ => 0) = 0.
Proof.
  induction l as [| a l IH]; [reflexivity |].
  rewrite big_sum_cons, IH. lia.
Qed.

Lemma big_sum_add : forall (l : list nat) (g h : nat -> Z),
  big_sum l (fun x => g x + h x) = big_sum l g + big_sum l h.
Proof.
  induction l as [| a l IH]; intros g h.
  - rewrite !big_sum_nil. reflexivity.
  - rewrite !big_sum_cons, IH. lia.
Qed.

Lemma big_sum_ext : forall (l : list nat) (g1 g2 : nat -> Z),
  (forall x, In x l -> g1 x = g2 x) -> big_sum l g1 = big_sum l g2.
Proof.
  induction l as [| a l IH]; intros g1 g2 H; [reflexivity |].
  rewrite !big_sum_cons.
  rewrite (H a (or_introl eq_refl)).
  rewrite (IH g1 g2) by (intros x Hx; apply H; right; exact Hx).
  reflexivity.
Qed.

Lemma big_sum_swap : forall (l1 l2 : list nat) (g : nat -> nat -> Z),
  big_sum l1 (fun i => big_sum l2 (fun j => g i j)) =
  big_sum l2 (fun j => big_sum l1 (fun i => g i j)).
Proof.
  induction l1 as [| a l1 IH]; intros l2 g.
  - rewrite big_sum_nil.
    rewrite (big_sum_ext l2 (fun j => big_sum [] (fun i => g i j)) (fun _ => 0))
      by (intros; reflexivity).
    rewrite big_sum_zero. reflexivity.
  - rewrite big_sum_cons, IH.
    rewrite (big_sum_ext l2 (fun j => big_sum (a :: l1) (fun i => g i j))
      (fun j => g a j + big_sum l1 (fun i => g i j)))
      by (intros x _; apply (big_sum_cons a l1 (fun i => g i x))).
    rewrite big_sum_add. reflexivity.
Qed.

Lemma big_sum_off_point : forall (l : list nat) (i0 : nat) (v : nat -> Z),
  ~ In i0 l ->
  big_sum l (fun i => if Nat.eqb i i0 then v i else 0) = 0.
Proof.
  induction l as [| b l IH]; intros i0 v Hn; [reflexivity |].
  rewrite big_sum_cons.
  destruct (Nat.eqb b i0) eqn:E.
  - apply Nat.eqb_eq in E. subst b. exfalso. apply Hn. left. reflexivity.
  - rewrite IH by (intro H; apply Hn; right; exact H). lia.
Qed.

Lemma big_sum_single : forall (l : list nat) (i0 : nat) (v : nat -> Z),
  NoDup l -> In i0 l ->
  big_sum l (fun i => if Nat.eqb i i0 then v i else 0) = v i0.
Proof.
  induction l as [| a l IH]; intros i0 v Hnd Hin; [destruct Hin |].
  inversion Hnd as [| ? ? Hnotin Hnd']; subst.
  rewrite big_sum_cons.
  destruct (Nat.eqb a i0) eqn:E.
  - apply Nat.eqb_eq in E. subst a.
    rewrite big_sum_off_point by exact Hnotin. lia.
  - apply Nat.eqb_neq in E.
    destruct Hin as [Heq | Hin]; [exfalso; apply E; exact Heq |].
    rewrite (IH i0 v Hnd' Hin). lia.
Qed.

Definition xor_scatter (n : nat) (f : nat -> nat -> Z) (k : nat) : Z :=
  big_sum (seq 0 n) (fun i =>
    big_sum (seq 0 n) (fun j => if Nat.eqb (Nat.lxor i j) k then f i j else 0)).

Definition xor_gather (n : nat) (f : nat -> nat -> Z) (k : nat) : Z :=
  big_sum (seq 0 n) (fun j => f (Nat.lxor k j) j).

Theorem scatter_equals_gather : forall (m : nat) (f : nat -> nat -> Z) (k : nat),
  (k < 2 ^ m)%nat -> xor_scatter (2 ^ m) f k = xor_gather (2 ^ m) f k.
Proof.
  intros m f k Hk. unfold xor_scatter, xor_gather.
  rewrite big_sum_swap.
  apply big_sum_ext. intros j Hj. apply in_seq in Hj.
  assert (Hj2 : (j < 2 ^ m)%nat) by lia.
  transitivity (big_sum (seq 0 (2 ^ m))
    (fun i => if Nat.eqb i (Nat.lxor k j) then f i j else 0)).
  - apply big_sum_ext. intros i _.
    destruct (Nat.eqb (Nat.lxor i j) k) eqn:E1, (Nat.eqb i (Nat.lxor k j)) eqn:E2;
      try reflexivity.
    + apply Nat.eqb_eq in E1. apply Nat.eqb_neq in E2. exfalso.
      apply E2. apply lxor_solve. exact E1.
    + apply Nat.eqb_neq in E1. apply Nat.eqb_eq in E2. exfalso.
      apply E1. apply lxor_solve. exact E2.
  - apply (big_sum_single (seq 0 (2 ^ m)) (Nat.lxor k j) (fun i => f i j)).
    + apply seq_NoDup.
    + apply in_seq. split; [lia |]. simpl.
      apply lxor_below_pow2; assumption.
Qed.
