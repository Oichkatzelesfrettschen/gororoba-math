(* The delegation model of the confine statement inventories.

   Convention. A subject is named by a string ("Thread_7"), an object by a
   string ("Thread 7", "arena_0"), and a right is a triple of a subject, an
   object and an action. A subject that holds Grant on an object delegates
   through the subject that object names (its owner). reachable_delegation
   is the least relation that contains the held rights and is closed under
   one step of delegation. The inventories state, for each right of a
   system, that a held right is reachable; that is the constructor
   rd_direct, for every rights relation.

   Chain n is the system the inventories enumerate: n threads, thread i
   holding Send, Receive and Map on its own object, Send and Grant on the
   object of thread i + 1, and thread 16 k holding Map on arena k. Its
   reachable rights are exactly the rights held at or above the subject's
   index (chain_reachable_iff), so delegation never reaches a lower thread
   (chain_confined_thread) and an arena only from at or below its holder
   (chain_confined_arena). *)

From Stdlib Require Import String List Arith Lia DecimalString Decimal DecimalNat.
Import ListNotations.

Open Scope string_scope.

Inductive Action : Type :=
| Send
| Receive
| Map
| Grant.

Module Type RIGHTS.
  Parameter has_right : string -> string -> Action -> Prop.
  Parameter owner : string -> string -> Prop.
End RIGHTS.

Module Reachability (R : RIGHTS).
  Import R.

  Inductive reachable_delegation : string -> string -> Action -> Prop :=
  | rd_direct : forall s o a, has_right s o a -> reachable_delegation s o a
  | rd_grant : forall s g t o a,
      has_right s g Grant -> owner g t -> reachable_delegation t o a ->
      reachable_delegation s o a.
End Reachability.

Definition decimal (i : nat) : string :=
  NilEmpty.string_of_uint (Nat.to_uint i).

Lemma decimal_inj : forall i j, decimal i = decimal j -> i = j.
Proof.
  intros i j H. unfold decimal in H.
  assert (E : Some (Nat.to_uint i) = Some (Nat.to_uint j)).
  { rewrite <- (NilEmpty.usu (Nat.to_uint i)), <- (NilEmpty.usu (Nat.to_uint j)).
    now rewrite H. }
  injection E as E.
  rewrite <- (Unsigned.of_to i), <- (Unsigned.of_to j). now rewrite E.
Qed.

Definition subject (i : nat) : string := "Thread_" ++ decimal i.
Definition thread_object (i : nat) : string := "Thread " ++ decimal i.
Definition arena (k : nat) : string := "arena_" ++ decimal k.

Lemma subject_inj : forall i j, subject i = subject j -> i = j.
Proof. intros i j H. apply decimal_inj. unfold subject in H. cbn in H. now inversion H. Qed.

Lemma thread_object_inj : forall i j, thread_object i = thread_object j -> i = j.
Proof. intros i j H. apply decimal_inj. unfold thread_object in H. cbn in H. now inversion H. Qed.

Lemma arena_inj : forall i j, arena i = arena j -> i = j.
Proof. intros i j H. apply decimal_inj. unfold arena in H. cbn in H. now inversion H. Qed.

Lemma thread_object_not_arena : forall i k, thread_object i <> arena k.
Proof. intros i k H. unfold thread_object, arena in H. cbn in H. discriminate H. Qed.

Ltac names :=
  repeat match goal with
  | H : subject _ = subject _ |- _ => apply subject_inj in H
  | H : thread_object _ = thread_object _ |- _ => apply thread_object_inj in H
  | H : arena _ = arena _ |- _ => apply arena_inj in H
  | H : decimal _ = decimal _ |- _ => apply decimal_inj in H
  | H : thread_object _ = arena _ |- _ =>
      exfalso; exact (thread_object_not_arena _ _ H)
  | H : arena _ = thread_object _ |- _ =>
      exfalso; exact (thread_object_not_arena _ _ (eq_sym H))
  end.

Inductive chain_right (n : nat) : string -> string -> Action -> Prop :=
| cr_own : forall i a, i < n -> a <> Grant ->
    chain_right n (subject i) (thread_object i) a
| cr_next_send : forall i, S i < n ->
    chain_right n (subject i) (thread_object (S i)) Send
| cr_next_grant : forall i, S i < n ->
    chain_right n (subject i) (thread_object (S i)) Grant
| cr_arena : forall k, 16 * k < n ->
    chain_right n (subject (16 * k)) (arena k) Map.

Definition chain_owner (o t : string) : Prop :=
  exists i, o = thread_object i /\ t = subject i.

(* The rights of thread i in the order the inventories list them. *)
Definition thread_rights (n i : nat) : list (string * string * Action) :=
  [(subject i, thread_object i, Send);
   (subject i, thread_object i, Receive);
   (subject i, thread_object i, Map)]
  ++ (if (S i <? n)%nat
      then [(subject i, thread_object (S i), Send);
            (subject i, thread_object (S i), Grant)]
      else [])
  ++ (if (i mod 16 =? 0)%nat then [(subject i, arena (i / 16)%nat, Map)] else []).

Definition chain_table (n : nat) : list (string * string * Action) :=
  flat_map (thread_rights n) (seq 0 n).

Lemma chain_table_spec : forall n s o a,
  In (s, o, a) (chain_table n) <-> chain_right n s o a.
Proof.
  intros n s o a. unfold chain_table. rewrite in_flat_map. split.
  - intros [i [Hi H]]. apply in_seq in Hi. unfold thread_rights in H.
    repeat (apply in_app_or in H; destruct H as [H | H]).
    + cbn in H. repeat destruct H as [H | H]; try contradiction;
        injection H as <- <- <-; apply cr_own; (lia || discriminate).
    + destruct (S i <? n)%nat eqn:E; [| contradiction].
      apply Nat.ltb_lt in E. cbn in H.
      repeat destruct H as [H | H]; try contradiction;
        injection H as <- <- <-; now constructor.
    + destruct (i mod 16 =? 0)%nat eqn:E; [| contradiction].
      apply Nat.eqb_eq in E. cbn in H. destruct H as [H | H]; [| contradiction].
      injection H as <- <- <-.
      assert (Hk : i = 16 * (i / 16)).
      { pose proof (Nat.div_mod_eq i 16). lia. }
      rewrite Hk at 1. apply cr_arena. lia.
  - intros H. destruct H as [i a Hi Ha | i Hi | i Hi | k Hk].
    + exists i. split; [apply in_seq; lia |]. unfold thread_rights.
      apply in_or_app. left. destruct a; cbn; tauto.
    + exists i. split; [apply in_seq; lia |]. unfold thread_rights.
      apply in_or_app. right. apply in_or_app. left.
      apply Nat.ltb_lt in Hi. rewrite Hi. cbn. tauto.
    + exists i. split; [apply in_seq; lia |]. unfold thread_rights.
      apply in_or_app. right. apply in_or_app. left.
      apply Nat.ltb_lt in Hi. rewrite Hi. cbn. tauto.
    + exists (16 * k). split; [apply in_seq; lia |]. unfold thread_rights.
      apply in_or_app. right. apply in_or_app. right.
      replace ((16 * k) mod 16) with 0
        by (symmetry; rewrite Nat.mul_comm; apply Nat.Div0.mod_mul).
      replace (16 * k / 16) with k
        by (symmetry; rewrite Nat.mul_comm; apply Nat.div_mul; discriminate).
      cbn. tauto.
Qed.

Lemma chain_table_held : forall n,
  Forall (fun r => chain_right n (fst (fst r)) (snd (fst r)) (snd r))
    (chain_table n).
Proof.
  intros n. apply Forall_forall. intros [[s o] a] H.
  now apply chain_table_spec.
Qed.

Module Type SIZE.
  Parameter n : nat.
End SIZE.

Module ChainRights (N : SIZE) <: RIGHTS.
  Definition has_right := chain_right N.n.
  Definition owner := chain_owner.
End ChainRights.

Module Chain (N : SIZE).
  Module R := ChainRights N.
  Module D := Reachability R.
  Import N R D.

  Lemma chain_right_subject : forall s o a,
    chain_right n s o a -> exists i, s = subject i /\ i < n.
  Proof.
    intros s o a H. destruct H as [i a Hi _ | i Hi | i Hi | k Hk];
      eexists; split; try reflexivity; lia.
  Qed.

  Lemma grant_is_next : forall i g t,
    chain_right n (subject i) g Grant -> chain_owner g t ->
    t = subject (S i) /\ S i < n.
  Proof.
    intros i g t H [j [Hg Ht]]. subst g t.
    inversion H; names; subst; try congruence. now split.
  Qed.

  Lemma reach_up : forall d i o a,
    chain_right n (subject (i + d)) o a ->
    reachable_delegation (subject i) o a.
  Proof.
    induction d as [| d IH]; intros i o a Hr.
    - rewrite Nat.add_0_r in Hr. now apply rd_direct.
    - destruct (chain_right_subject _ _ _ Hr) as [j [Hj Hlt]].
      apply subject_inj in Hj. subst j.
      apply (rd_grant (subject i) (thread_object (S i)) (subject (S i))).
      + apply cr_next_grant. lia.
      + now exists (S i).
      + apply IH. now replace (S i + d) with (i + S d) by lia.
  Qed.

  Lemma reach_down : forall s o a,
    reachable_delegation s o a ->
    forall i, s = subject i ->
    exists j, i <= j /\ chain_right n (subject j) o a.
  Proof.
    intros s o a H.
    induction H as [s o a Hr | s g t o a Hg Ho _ IH]; intros i ->.
    - exists i. now split.
    - destruct (grant_is_next _ _ _ Hg Ho) as [-> _].
      destruct (IH (S i) eq_refl) as [j [Hj Hr]].
      exists j. split; [lia | exact Hr].
  Qed.

  (* The rights a thread reaches by delegation are the rights held by the
     threads at or above it. *)
  Theorem chain_reachable_iff : forall i o a,
    reachable_delegation (subject i) o a <->
    exists j, i <= j /\ chain_right n (subject j) o a.
  Proof.
    intros i o a. split.
    - intros H. now apply (reach_down _ _ _ H).
    - intros [j [Hij Hr]]. apply (reach_up (j - i)).
      now replace (i + (j - i)) with j by lia.
  Qed.

  Theorem chain_confined_thread : forall i j a,
    reachable_delegation (subject i) (thread_object j) a -> i <= j.
  Proof.
    intros i j a H. apply chain_reachable_iff in H.
    destruct H as [h [Hih Hr]].
    inversion Hr; names; subst; lia.
  Qed.

  Theorem chain_confined_arena : forall i k a,
    reachable_delegation (subject i) (arena k) a -> a = Map /\ i <= 16 * k.
  Proof.
    intros i k a H. apply chain_reachable_iff in H.
    destruct H as [h [Hih Hr]].
    inversion Hr; names; subst. split; [reflexivity | lia].
  Qed.

  (* Every right of the table is reachable from its own subject, with no
     hypothesis left. *)
  Theorem chain_table_reachable :
    Forall (fun r => reachable_delegation (fst (fst r)) (snd (fst r)) (snd r))
      (chain_table n).
  Proof.
    apply Forall_forall. intros [[s o] a] H.
    apply rd_direct. now apply chain_table_spec.
  Qed.

  (* Grant itself is reachable only on the objects of higher threads, so no
     thread delegates to itself or downward. *)
  Theorem chain_grant_strictly_up : forall i j,
    reachable_delegation (subject i) (thread_object j) Grant -> i < j.
  Proof.
    intros i j H. apply chain_reachable_iff in H.
    destruct H as [h [Hih Hr]].
    inversion Hr; names; subst; try congruence; lia.
  Qed.
End Chain.
