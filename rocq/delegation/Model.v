(* The delegation model of the confine statement inventories.

   Convention. A subject is named by a string ("Thread_7"), an object by a
   string ("Thread 7", "arena_0"), and a right is a triple of a subject, an
   object and an action. A subject that holds Grant on an object delegates
   through the subject that object names (its owner).

   Three semantics of delegation over one rights relation:
   - reachable_delegation: the least relation that contains the held rights
     and is closed under a Grant step, so a delegated Grant delegates again;
   - restricted_delegation P: the same closure where a step conveys only an
     action that satisfies P (P a := a <> Grant keeps Grant from travelling);
   - single_delegation: a Grant step conveys only what the owner holds.
   A held right is reachable in each (the constructors rd_direct, rr_direct,
   sd_direct), for every rights relation. The inventories state exactly
   that, so they hold in all three and distinguish none of them.

   chain_right p n is the system the inventories enumerate with p = 16:
   n threads, thread i holding Send, Receive and Map on its own object, Send
   and Grant on the object of thread i + 1, and thread p k holding Map on
   arena k. For every n and p:
   - chain_reachable_iff: a thread reaches the rights held at or above it;
   - chain_restricted_iff: under P, its own rights and the P-rights above;
   - chain_single_iff: its own rights and those of the next thread;
   - chain_grant_iff, chain_restricted_grant: Grant is reachable on every
     higher thread object in the first semantics and only on the next one
     under P a := a <> Grant. *)

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

  Inductive restricted_delegation (P : Action -> Prop) :
    string -> string -> Action -> Prop :=
  | rr_direct : forall s o a,
      has_right s o a -> restricted_delegation P s o a
  | rr_grant : forall s g t o a,
      has_right s g Grant -> owner g t -> P a ->
      restricted_delegation P t o a -> restricted_delegation P s o a.

  Inductive single_delegation : string -> string -> Action -> Prop :=
  | sd_direct : forall s o a, has_right s o a -> single_delegation s o a
  | sd_grant : forall s g t o a,
      has_right s g Grant -> owner g t -> has_right t o a ->
      single_delegation s o a.

  Lemma restricted_reachable : forall P s o a,
    restricted_delegation P s o a -> reachable_delegation s o a.
  Proof.
    intros P s o a H. induction H as [s o a H | s g t o a Hg Ho _ _ IH].
    - now apply rd_direct.
    - now apply (rd_grant s g t).
  Qed.

  Lemma unrestricted_iff : forall s o a,
    restricted_delegation (fun _ => True) s o a <-> reachable_delegation s o a.
  Proof.
    intros s o a. split; [apply restricted_reachable |].
    intros H. induction H as [s o a H | s g t o a Hg Ho _ IH].
    - now apply rr_direct.
    - now apply (rr_grant _ s g t).
  Qed.

  Lemma single_reachable : forall s o a,
    single_delegation s o a -> reachable_delegation s o a.
  Proof.
    intros s o a H. destruct H as [s o a H | s g t o a Hg Ho Ht].
    - now apply rd_direct.
    - apply (rd_grant s g t); [assumption | assumption | now apply rd_direct].
  Qed.
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

Inductive chain_right (p n : nat) : string -> string -> Action -> Prop :=
| cr_own : forall i a, i < n -> a <> Grant ->
    chain_right p n (subject i) (thread_object i) a
| cr_next_send : forall i, S i < n ->
    chain_right p n (subject i) (thread_object (S i)) Send
| cr_next_grant : forall i, S i < n ->
    chain_right p n (subject i) (thread_object (S i)) Grant
| cr_arena : forall k, p * k < n ->
    chain_right p n (subject (p * k)) (arena k) Map.

Definition chain_owner (o t : string) : Prop :=
  exists i, o = thread_object i /\ t = subject i.

(* The rights of thread i in the order the inventories list them. *)
Definition thread_rights (p n i : nat) : list (string * string * Action) :=
  [(subject i, thread_object i, Send);
   (subject i, thread_object i, Receive);
   (subject i, thread_object i, Map)]
  ++ (if (S i <? n)%nat
      then [(subject i, thread_object (S i), Send);
            (subject i, thread_object (S i), Grant)]
      else [])
  ++ (if (i mod p =? 0)%nat then [(subject i, arena (i / p)%nat, Map)] else []).

Definition chain_table (p n : nat) : list (string * string * Action) :=
  flat_map (thread_rights p n) (seq 0 n).

Lemma chain_table_spec : forall p n s o a, p <> 0 ->
  In (s, o, a) (chain_table p n) <-> chain_right p n s o a.
Proof.
  intros p n s o a Hp. unfold chain_table. rewrite in_flat_map. split.
  - intros [i [Hi H]]. apply in_seq in Hi. unfold thread_rights in H.
    repeat (apply in_app_or in H; destruct H as [H | H]).
    + cbn in H. repeat destruct H as [H | H]; try contradiction;
        injection H as <- <- <-; apply cr_own; (lia || discriminate).
    + destruct (S i <? n)%nat eqn:E; [| contradiction].
      apply Nat.ltb_lt in E. cbn in H.
      repeat destruct H as [H | H]; try contradiction;
        injection H as <- <- <-; now constructor.
    + destruct (i mod p =? 0)%nat eqn:E; [| contradiction].
      apply Nat.eqb_eq in E. cbn in H. destruct H as [H | H]; [| contradiction].
      injection H as <- <- <-.
      assert (Hk : i = p * (i / p)).
      { pose proof (Nat.div_mod_eq i p). lia. }
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
    + exists (p * k). split; [apply in_seq; lia |]. unfold thread_rights.
      apply in_or_app. right. apply in_or_app. right.
      replace ((p * k) mod p) with 0
        by (symmetry; rewrite Nat.mul_comm; apply Nat.Div0.mod_mul).
      replace (p * k / p) with k
        by (symmetry; rewrite Nat.mul_comm; now apply Nat.div_mul).
      cbn. tauto.
Qed.

Lemma chain_table_held : forall p n, p <> 0 ->
  Forall (fun r => chain_right p n (fst (fst r)) (snd (fst r)) (snd r))
    (chain_table p n).
Proof.
  intros p n Hp. apply Forall_forall. intros [[s o] a] H.
  now apply chain_table_spec.
Qed.

Module Type SIZE.
  Parameter period : nat.
  Parameter n : nat.
End SIZE.

Module ChainRights (N : SIZE) <: RIGHTS.
  Definition has_right := chain_right N.period N.n.
  Definition owner := chain_owner.
End ChainRights.

Module Chain (N : SIZE).
  Module R := ChainRights N.
  Module D := Reachability R.
  Import N R D.

  Local Abbreviation held := (chain_right period n).

  Lemma chain_right_subject : forall s o a,
    held s o a -> exists i, s = subject i /\ i < n.
  Proof.
    intros s o a H. destruct H as [i a Hi _ | i Hi | i Hi | k Hk];
      eexists; split; try reflexivity; lia.
  Qed.

  Lemma grant_is_next : forall i g t,
    held (subject i) g Grant -> chain_owner g t ->
    t = subject (S i) /\ S i < n.
  Proof.
    intros i g t H [j [Hg Ht]]. subst g t.
    inversion H; names; subst; try congruence. now split.
  Qed.

  Lemma restricted_up : forall (P : Action -> Prop) d i o a,
    P a -> held (subject (i + S d)) o a ->
    restricted_delegation P (subject i) o a.
  Proof.
    intros P. induction d as [| d IH]; intros i o a Pa Hr;
      destruct (chain_right_subject _ _ _ Hr) as [j [Hj Hlt]];
      apply subject_inj in Hj; subst j;
      apply (rr_grant P (subject i) (thread_object (S i)) (subject (S i)));
      try (apply cr_next_grant; lia); try (now exists (S i)); try assumption.
    - apply rr_direct. now replace (S i) with (i + 1) by lia.
    - apply IH; [assumption |]. now replace (S i + S d) with (i + S (S d)) by lia.
  Qed.

  (* Under a restriction P a thread reaches its own rights and the rights
     on a P-action held strictly above it. *)
  Theorem chain_restricted_iff : forall (P : Action -> Prop) i o a,
    restricted_delegation P (subject i) o a <->
    held (subject i) o a \/
    (P a /\ exists j, i < j /\ held (subject j) o a).
  Proof.
    intros P i o a. split.
    - intros H. remember (subject i) as s eqn:Es. revert i Es.
      induction H as [s o a Hr | s g t o a Hg Ho Pa _ IH]; intros i ->.
      + now left.
      + destruct (grant_is_next _ _ _ Hg Ho) as [-> _]. right. split; [exact Pa |].
        destruct (IH (S i) eq_refl) as [Hr | [_ [j [Hj Hr]]]].
        * exists (S i). split; [lia | exact Hr].
        * exists j. split; [lia | exact Hr].
    - intros [Hr | [Pa [j [Hj Hr]]]].
      + now apply rr_direct.
      + apply (restricted_up P (j - S i)); [exact Pa |].
        now replace (i + S (j - S i)) with j by lia.
  Qed.

  (* The rights a thread reaches by delegation are the rights held by the
     threads at or above it. *)
  Theorem chain_reachable_iff : forall i o a,
    reachable_delegation (subject i) o a <->
    exists j, i <= j /\ held (subject j) o a.
  Proof.
    intros i o a. rewrite <- unrestricted_iff, chain_restricted_iff. split.
    - intros [Hr | [_ [j [Hj Hr]]]].
      + exists i. now split.
      + exists j. split; [lia | exact Hr].
    - intros [j [Hj Hr]]. destruct (Nat.eq_dec i j) as [-> | Hne].
      + now left.
      + right. split; [exact I |]. exists j. split; [lia | exact Hr].
  Qed.

  (* When a Grant step conveys only what the owner holds, a thread reaches
     its own rights and those of the next thread. *)
  Theorem chain_single_iff : forall i o a,
    single_delegation (subject i) o a <->
    held (subject i) o a \/ held (subject (S i)) o a.
  Proof.
    intros i o a. split.
    - intros H. remember (subject i) as s eqn:Es.
      destruct H as [s o a Hr | s g t o a Hg Ho Ht]; subst s.
      + now left.
      + destruct (grant_is_next _ _ _ Hg Ho) as [-> _]. now right.
    - intros [Hr | Hr].
      + now apply sd_direct.
      + destruct (chain_right_subject _ _ _ Hr) as [j [Hj Hlt]].
        apply subject_inj in Hj. subst j.
        apply (sd_grant (subject i) (thread_object (S i)) (subject (S i)));
          [now apply cr_next_grant | now exists (S i) | exact Hr].
  Qed.

  Theorem chain_confined_thread : forall i j a,
    reachable_delegation (subject i) (thread_object j) a -> i <= j.
  Proof.
    intros i j a H. apply chain_reachable_iff in H.
    destruct H as [h [Hih Hr]].
    inversion Hr; names; subst; lia.
  Qed.

  Theorem chain_confined_arena : forall i k a,
    reachable_delegation (subject i) (arena k) a ->
    a = Map /\ i <= period * k.
  Proof.
    intros i k a H. apply chain_reachable_iff in H.
    destruct H as [h [Hih Hr]].
    inversion Hr; names; subst. split; [reflexivity | lia].
  Qed.

  (* Where the semantics differ. A delegated Grant delegates again: Grant
     is reachable on the object of every higher thread. *)
  Theorem chain_grant_iff : forall i j,
    reachable_delegation (subject i) (thread_object j) Grant <->
    i < j /\ j < n.
  Proof.
    intros i j. rewrite chain_reachable_iff. split.
    - intros [h [Hih Hr]]. inversion Hr; names; subst; try congruence; lia.
    - intros [Hij Hjn]. exists (j - 1). split; [lia |].
      replace j with (S (j - 1)) at 2 by lia. apply cr_next_grant. lia.
  Qed.

  (* When Grant does not travel, a thread holds Grant on the next thread's
     object and reaches no other. *)
  Theorem chain_restricted_grant : forall i j,
    restricted_delegation (fun a => a <> Grant) (subject i) (thread_object j) Grant <->
    j = S i /\ j < n.
  Proof.
    intros i j. rewrite chain_restricted_iff. split.
    - intros [Hr | [Hne _]]; [| congruence].
      inversion Hr; names; subst; try congruence. now split.
    - intros [-> Hlt]. left. now apply cr_next_grant.
  Qed.

  (* The other actions travel under that restriction as they do without
     it. *)
  Theorem chain_restricted_other : forall i o a, a <> Grant ->
    (restricted_delegation (fun a => a <> Grant) (subject i) o a <->
     reachable_delegation (subject i) o a).
  Proof.
    intros i o a Ha. rewrite chain_restricted_iff, chain_reachable_iff. split.
    - intros [Hr | [_ [j [Hj Hr]]]].
      + exists i. now split.
      + exists j. split; [lia | exact Hr].
    - intros [j [Hj Hr]]. destruct (Nat.eq_dec i j) as [-> | Hne].
      + now left.
      + right. split; [exact Ha |]. exists j. split; [lia | exact Hr].
  Qed.

  (* Two threads up, the closure reaches a right that one step does not. *)
  Theorem chain_single_weaker : forall i, S (S i) < n ->
    reachable_delegation (subject i) (thread_object (S (S i))) Receive /\
    ~ single_delegation (subject i) (thread_object (S (S i))) Receive.
  Proof.
    intros i Hi. split.
    - apply chain_reachable_iff. exists (S (S i)). split; [lia |].
      apply cr_own; [exact Hi | discriminate].
    - intros H. apply chain_single_iff in H.
      destruct H as [Hr | Hr]; inversion Hr; names; subst; lia.
  Qed.

  (* Every right of the table is reachable from its own subject, with no
     hypothesis left. *)
  Theorem chain_table_reachable : period <> 0 ->
    Forall (fun r => reachable_delegation (fst (fst r)) (snd (fst r)) (snd r))
      (chain_table period n).
  Proof.
    intros Hp. apply Forall_forall. intros [[s o] a] H.
    apply rd_direct. now apply chain_table_spec.
  Qed.
End Chain.
