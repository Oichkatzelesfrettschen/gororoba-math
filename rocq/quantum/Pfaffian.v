(** Pfaffians over a commutative ring, by expansion along the first index.

    Convention: a function M : nat -> nat -> R is read as a matrix and a
    list l of indices as the rows and columns kept. pf M [] = 1, and
    pf M (x :: r) is the sum over k < length r of (-1)^k M x r_k times
    pf M (r with its k-th entry removed). A list of odd length has
    Pfaffian 0. The results hold for every skew M (M i j = - M j i). *)

From Stdlib Require Import List Ring Field Lia PeanoNat Permutation Wf_nat.
Require Import CdTowerRing.
Import ListNotations.

Module PfaffianTheory (D : CommutativeRing).

Add Ring pf_ring : D.ring_th.

Declare Scope pf_scope.
Delimit Scope pf_scope with pf.
Local Infix "+" := D.add : pf_scope.
Local Infix "*" := D.mul : pf_scope.
Local Infix "-" := D.sub : pf_scope.
Local Notation "- x" := (D.opp x) : pf_scope.

(** Finite sums over k < n. *)
Fixpoint sumk (n : nat) (f : nat -> D.t) : D.t :=
  match n with O => D.zero | S m => D.add (sumk m f) (f m) end.

Lemma sumk_ext n f g : (forall k, k < n -> f k = g k) -> sumk n f = sumk n g.
Proof.
  induction n as [|n IH]; intros H; simpl; [reflexivity|].
  rewrite IH by (intros; apply H; lia). rewrite (H n) by lia. reflexivity.
Qed.

Lemma sumk_add n f g : sumk n (fun k => (f k + g k)%pf) = (sumk n f + sumk n g)%pf.
Proof. induction n as [|n IH]; simpl; [ring|]. rewrite IH. ring. Qed.

Lemma sumk_scale n c f : sumk n (fun k => (c * f k)%pf) = (c * sumk n f)%pf.
Proof. induction n as [|n IH]; simpl; [ring|]. rewrite IH. ring. Qed.

Lemma sumk_opp n f : sumk n (fun k => (- f k)%pf) = (- sumk n f)%pf.
Proof. induction n as [|n IH]; simpl; [ring|]. rewrite IH. ring. Qed.

Lemma sumk_zero n f : (forall k, k < n -> f k = D.zero) -> sumk n f = D.zero.
Proof.
  induction n as [|n IH]; intros H; simpl; [reflexivity|].
  rewrite IH by (intros; apply H; lia). rewrite H by lia. ring.
Qed.

Lemma sumk_first n f : sumk (S n) f = (f 0 + sumk n (fun k => f (S k)))%pf.
Proof.
  induction n as [|n IH]; simpl in *; [ring|]. rewrite IH. ring.
Qed.

Lemma sumk_swap n m f :
  sumk n (fun j => sumk m (fun p => f j p)) = sumk m (fun p => sumk n (fun j => f j p)).
Proof.
  induction n as [|n IH]; simpl.
  - symmetry. apply sumk_zero. reflexivity.
  - rewrite IH. rewrite <- sumk_add. reflexivity.
Qed.

(** Exactly one nonzero term. *)
Lemma sumk_single n f q : q < n -> (forall k, k < n -> k <> q -> f k = D.zero) -> sumk n f = f q.
Proof.
  induction n as [|n IH]; intros Hq H; [lia|]. simpl.
  destruct (Nat.eq_dec q n) as [->|Hne].
  - rewrite sumk_zero by (intros; apply H; lia). ring.
  - rewrite IH by (try lia; intros; apply H; lia). rewrite (H n) by lia. ring.
Qed.

(** Reindexing by the transposition of q and q + 1. *)
Definition tau (q k : nat) : nat :=
  if Nat.eqb k q then S q else if Nat.eqb k (S q) then q else k.

Lemma sumk_split a b f : sumk (a + b) f = (sumk a f + sumk b (fun k => f (a + k)%nat))%pf.
Proof.
  induction b as [|b IH]; simpl.
  - rewrite Nat.add_0_r. ring.
  - rewrite Nat.add_succ_r. simpl. rewrite IH. ring.
Qed.

Lemma tau_lt q k : k < q -> tau q k = k.
Proof.
  intros H. unfold tau.
  replace (Nat.eqb k q) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb k (S q)) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.

Lemma tau_gt q k : S q < k -> tau q k = k.
Proof.
  intros H. unfold tau.
  replace (Nat.eqb k q) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb k (S q)) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.

Lemma tau_q q : tau q q = S q.
Proof. unfold tau. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma tau_Sq q : tau q (S q) = q.
Proof.
  unfold tau. replace (Nat.eqb (S q) q) with false by (symmetry; apply Nat.eqb_neq; lia).
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma sumk_tau n q f : S q < n -> sumk n (fun k => f (tau q k)) = sumk n f.
Proof.
  induction n as [|n IH]; intros Hq; [lia|].
  destruct (Nat.eq_dec n (S q)) as [E|E].
  - subst n. cbn [sumk].
    rewrite (sumk_ext q (fun k => f (tau q k)) f) by (intros; apply f_equal, tau_lt; lia).
    rewrite tau_q, tau_Sq. ring.
  - cbn [sumk]. rewrite IH by lia. rewrite tau_gt by lia. reflexivity.
Qed.

Definition sgn (k : nat) : D.t := if Nat.even k then D.one else D.opp D.one.

Lemma sgn_S k : sgn (S k) = D.opp (sgn k).
Proof. unfold sgn. rewrite Nat.even_succ, <- Nat.negb_even. destruct (Nat.even k); simpl; ring. Qed.

Lemma sgn_sq k : (sgn k * sgn k)%pf = D.one.
Proof. unfold sgn. destruct (Nat.even k); ring. Qed.

(** Removal of the entry at a position. *)
Fixpoint rem_at {A} (k : nat) (l : list A) {struct l} : list A :=
  match l with
  | [] => []
  | x :: r => match k with O => r | S k' => x :: rem_at k' r end
  end.

Lemma length_rem_at {A} k (l : list A) : k < length l -> length (rem_at k l) = pred (length l).
Proof.
  revert k. induction l as [|x r IH]; intros k Hk; simpl in *; [lia|].
  destruct k as [|k]; [reflexivity|]. simpl. rewrite IH by lia. destruct r; simpl in *; lia.
Qed.

Lemma nth_rem_at {A} k m (l : list A) d :
  nth m (rem_at k l) d = nth (if m <? k then m else S m) l d.
Proof.
  revert k m. induction l as [|x r IH]; intros k m.
  - assert (E : rem_at k ([] : list A) = []) by (destruct k; reflexivity). rewrite E.
    destruct (m <? k); destruct m; reflexivity.
  - destruct k as [|k]; simpl.
    + destruct m; reflexivity.
    + destruct m as [|m]; simpl; [reflexivity|]. rewrite IH.
      change (S m <? S k) with (m <? k). destruct (m <? k); reflexivity.
Qed.

Lemma rem_at_rem_at {A} p j (l : list A) :
  p < j -> rem_at p (rem_at j l) = rem_at (pred j) (rem_at p l).
Proof.
  revert p j. induction l as [|x r IH]; intros p j H; [reflexivity|].
  destruct j as [|j]; [lia|]. destruct p as [|p]; simpl.
  - destruct j; reflexivity.
  - destruct j as [|j]; [lia|]. simpl. f_equal. apply (IH p (S j)). lia.
Qed.

(** The transposition of the entries at positions q and q + 1. *)
Fixpoint swap_at {A} (q : nat) (l : list A) {struct l} : list A :=
  match q, l with
  | O, x :: y :: r => y :: x :: r
  | S q', x :: r => x :: swap_at q' r
  | _, _ => l
  end.

Lemma tau_S q k : tau (S q) (S k) = S (tau q k).
Proof. unfold tau. simpl. destruct (Nat.eqb k q); [reflexivity|]. destruct (Nat.eqb k (S q)); reflexivity. Qed.

Lemma tau_S0 q : tau (S q) O = O.
Proof. reflexivity. Qed.

Lemma length_swap_at {A} q (l : list A) : length (swap_at q l) = length l.
Proof.
  revert l. induction q as [|q IH]; intros l.
  - destruct l as [|x [|y r]]; reflexivity.
  - destruct l as [|x r]; [reflexivity|]. simpl. rewrite IH. reflexivity.
Qed.

Lemma nth_swap_at {A} q (l : list A) k d :
  S q < length l -> nth k (swap_at q l) d = nth (tau q k) l d.
Proof.
  revert l k. induction q as [|q IH]; intros l k H.
  - destruct l as [|x [|y r]]; simpl in H; try lia.
    destruct k as [|[|k]]; reflexivity.
  - destruct l as [|x r]; simpl in H; [lia|]. destruct k as [|k]; [reflexivity|].
    simpl swap_at. rewrite tau_S. simpl nth. apply IH. lia.
Qed.

Lemma rem_at_swap_q {A} q (l : list A) : S q < length l -> rem_at q (swap_at q l) = rem_at (S q) l.
Proof.
  revert l. induction q as [|q IH]; intros l H.
  - destruct l as [|x [|y r]]; simpl in H; try lia. reflexivity.
  - destruct l as [|x r]; simpl in H; [lia|]. simpl. f_equal. apply IH. lia.
Qed.

Lemma rem_at_swap_Sq {A} q (l : list A) : S q < length l -> rem_at (S q) (swap_at q l) = rem_at q l.
Proof.
  revert l. induction q as [|q IH]; intros l H.
  - destruct l as [|x [|y r]]; simpl in H; try lia. reflexivity.
  - destruct l as [|x r]; simpl in H; [lia|]. simpl. f_equal. apply IH. lia.
Qed.

Lemma rem_at_swap_lt {A} q k (l : list A) :
  k < q -> S q < length l -> rem_at k (swap_at q l) = swap_at (pred q) (rem_at k l).
Proof.
  revert q l. induction k as [|k IH]; intros q l Hk H.
  - destruct q as [|q]; [lia|]. destruct l as [|x r]; simpl in H; [lia|]. reflexivity.
  - destruct q as [|q]; [lia|]. destruct l as [|x r]; simpl in H; [lia|].
    simpl. rewrite IH by lia. destruct q as [|q]; [lia|]. reflexivity.
Qed.

Lemma rem_at_swap_gt {A} q k (l : list A) :
  S q < k -> rem_at k (swap_at q l) = swap_at q (rem_at k l).
Proof.
  revert k l. induction q as [|q IH]; intros k l Hk.
  - destruct l as [|x [|y r]]; [reflexivity| |].
    + destruct k as [|[|k]]; try lia; reflexivity.
    + destruct k as [|[|k]]; try lia. reflexivity.
  - destruct l as [|x r]; [destruct k; reflexivity|]. destruct k as [|k]; [lia|].
    simpl. rewrite IH by lia. reflexivity.
Qed.

Section WithM.
Variable M : nat -> nat -> D.t.

Fixpoint pfn (n : nat) (l : list nat) : D.t :=
  match l with
  | [] => D.one
  | x :: r =>
      match n with
      | O => D.zero
      | S n' => sumk (length r) (fun k => (sgn k * M x (nth k r O) * pfn n' (rem_at k r))%pf)
      end
  end.

Definition pf (l : list nat) : D.t := pfn (length l) l.

Lemma pfn_fuel n m l : length l <= n -> length l <= m -> pfn n l = pfn m l.
Proof.
  revert m l. induction n as [|n IH]; intros m l Hn Hm.
  - destruct l; simpl in *; [destruct m; reflexivity | lia].
  - destruct l as [|x r]; [destruct m; reflexivity|]. destruct m as [|m]; [simpl in *; lia|].
    simpl. apply sumk_ext. intros k Hk. f_equal. apply IH;
    rewrite length_rem_at by lia; simpl in *; lia.
Qed.

Lemma pf_nil : pf [] = D.one.
Proof. reflexivity. Qed.

Lemma pf_cons x r :
  pf (x :: r) = sumk (length r) (fun k => (sgn k * M x (nth k r O) * pf (rem_at k r))%pf).
Proof.
  unfold pf at 1. simpl. apply sumk_ext. intros k Hk. f_equal. unfold pf.
  apply pfn_fuel; rewrite length_rem_at by lia; lia.
Qed.


Hypothesis M_skew : forall a b, M a b = D.opp (M b a).

(** Reindexing a sum over m < n - 1 as a sum over p < n that skips j. *)
Lemma sumk_skip n j g : j < n ->
  sumk (pred n) g = sumk n (fun p => if Nat.eqb p j then D.zero else g (if p <? j then p else pred p)).
Proof.
  intros Hj. replace n with (j + S (n - S j))%nat by lia.
  replace (pred (j + S (n - S j))) with (j + (n - S j))%nat by lia.
  rewrite !sumk_split. rewrite sumk_first.
  rewrite (sumk_ext j (fun p => if Nat.eqb p j then D.zero else g (if p <? j then p else pred p)) g).
  2:{ intros p Hp. replace (Nat.eqb p j) with false by (symmetry; apply Nat.eqb_neq; lia).
      replace (p <? j) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
  rewrite Nat.add_0_r, Nat.eqb_refl.
  rewrite (sumk_ext (n - S j) (fun k => if Nat.eqb (j + S k) j then D.zero
             else g (if j + S k <? j then (j + S k)%nat else pred (j + S k))) (fun k => g (j + k)%nat)).
  2:{ intros k Hk. replace (Nat.eqb (j + S k) j) with false by (symmetry; apply Nat.eqb_neq; lia).
      replace (j + S k <? j) with false by (symmetry; apply Nat.ltb_ge; lia). f_equal. lia. }
  ring.
Qed.

Definition rem2 (j p : nat) (l : list nat) : list nat :=
  rem_at (if p <? j then p else pred p) (rem_at j l).

Lemma rem2_sym j p l : j <> p -> rem2 j p l = rem2 p j l.
Proof.
  intros H. unfold rem2. destruct (p <? j) eqn:E1; destruct (j <? p) eqn:E2.
  - apply Nat.ltb_lt in E1, E2. lia.
  - apply Nat.ltb_lt in E1. apply rem_at_rem_at. exact E1.
  - apply Nat.ltb_lt in E2. symmetry. apply rem_at_rem_at. exact E2.
  - apply Nat.ltb_ge in E1, E2. lia.
Qed.

Definition kappa (j p : nat) : D.t :=
  D.mul (sgn (S j)) (if p <? j then sgn p else D.opp (sgn p)).

Lemma kappa_anti j p : j <> p -> kappa p j = D.opp (kappa j p).
Proof.
  intros H. unfold kappa. rewrite !sgn_S.
  destruct (p <? j) eqn:E1; destruct (j <? p) eqn:E2.
  - apply Nat.ltb_lt in E1, E2. lia.
  - ring.
  - ring.
  - apply Nat.ltb_ge in E1, E2. lia.
Qed.

Definition dbl (a b : nat) (l : list nat) : D.t :=
  sumk (length l) (fun j => sumk (length l) (fun p =>
    if Nat.eqb p j then D.zero
    else (kappa j p * M a (nth j l O) * M b (nth p l O) * pf (rem2 j p l))%pf)).

Lemma pf_cons2 a b l : pf (a :: b :: l) =
  (M a b * pf l + sumk (length l) (fun j => sgn (S j) * M a (nth j l O) * pf (b :: rem_at j l)))%pf.
Proof.
  rewrite pf_cons. cbn [length]. rewrite sumk_first. cbn [nth rem_at].
  replace (sgn 0) with D.one by reflexivity. ring.
Qed.

Lemma pf_two a b l : pf (a :: b :: l) = (M a b * pf l + dbl a b l)%pf.
Proof.
  rewrite pf_cons2. f_equal. unfold dbl. apply sumk_ext. intros j Hj.
  rewrite pf_cons. rewrite length_rem_at by lia.
  rewrite (sumk_skip (length l) j) by lia.
  rewrite <- sumk_scale. apply sumk_ext. intros p Hp.
  destruct (Nat.eqb p j) eqn:Epj; [ring|].
  apply Nat.eqb_neq in Epj.
  rewrite nth_rem_at. unfold rem2, kappa.
  destruct (p <? j) eqn:E.
  - rewrite E. ring.
  - apply Nat.ltb_ge in E.
    replace (pred p <? j) with false by (symmetry; apply Nat.ltb_ge; lia).
    replace (S (pred p)) with p by lia.
    replace (sgn (pred p)) with (D.opp (sgn p)).
    + ring.
    + destruct p as [|p']; [lia|]. simpl pred. rewrite sgn_S. ring.
Qed.

Lemma dbl_swap a b l : dbl b a l = D.opp (dbl a b l).
Proof.
  unfold dbl. rewrite sumk_swap. rewrite <- sumk_opp. apply sumk_ext. intros p Hp.
  rewrite <- sumk_opp. apply sumk_ext. intros j Hj.
  destruct (Nat.eq_dec p j) as [->|Hne].
  - rewrite Nat.eqb_refl. ring.
  - replace (Nat.eqb j p) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.eqb p j) with false by (symmetry; apply Nat.eqb_neq; lia).
    rewrite (kappa_anti j p) by lia. rewrite (rem2_sym p j) by lia. ring.
Qed.

Lemma pf_swap_head a b l : pf (b :: a :: l) = D.opp (pf (a :: b :: l)).
Proof. rewrite !pf_two, dbl_swap, (M_skew b a). ring. Qed.


Lemma pf_swap_at q l : S q < length l -> pf (swap_at q l) = D.opp (pf l).
Proof.
  remember (length l) as n eqn:En. revert q l En.
  induction n as [n IH] using (well_founded_induction lt_wf). intros q l En Hq.
  subst n. destruct q as [|q].
  - destruct l as [|a [|b r]]; simpl in Hq; try lia. simpl swap_at. apply pf_swap_head.
  - destruct l as [|x r]; simpl in Hq; [lia|]. simpl swap_at.
    rewrite !pf_cons. rewrite length_swap_at.
    rewrite <- (sumk_tau (length r) q (fun k => (sgn k * M x (nth k r O) * pf (rem_at k r))%pf)) by lia.
    rewrite <- sumk_opp.
    apply sumk_ext. intros k Hk.
    rewrite (nth_swap_at q r k O) by lia.
    destruct (Nat.lt_trichotomy k q) as [Hlt|[->|Hgt]].
    + rewrite tau_lt by lia. rewrite rem_at_swap_lt by lia.
      rewrite (IH (length (rem_at k r))); [ring | | reflexivity |].
      * rewrite length_rem_at by lia. simpl. lia.
      * rewrite length_rem_at by lia. destruct q; lia.
    + rewrite tau_q, rem_at_swap_q by lia. rewrite sgn_S. ring.
    + destruct (Nat.eq_dec k (S q)) as [->|Hne].
      * rewrite tau_Sq, rem_at_swap_Sq by lia. rewrite sgn_S. ring.
      * rewrite tau_gt by lia. rewrite rem_at_swap_gt by lia.
        rewrite (IH (length (rem_at k r))); [ring | | reflexivity |].
        -- rewrite length_rem_at by lia. simpl. lia.
        -- rewrite length_rem_at by lia. lia.
Qed.

(** Moving the entry at position k to the front multiplies pf by (-1)^k. *)
Lemma pf_move_front k l : k < length l -> pf (nth k l O :: rem_at k l) = (sgn k * pf l)%pf.
Proof.
  revert l. induction k as [|k IH]; intros l Hk.
  - destruct l as [|x r]; simpl in Hk; [lia|]. simpl. unfold sgn; simpl. ring.
  - rewrite <- (rem_at_swap_q k l) by lia.
    replace (nth (S k) l O) with (nth k (swap_at k l) O)
      by (rewrite nth_swap_at by lia; rewrite tau_q; reflexivity).
    rewrite IH by (rewrite length_swap_at; lia).
    rewrite pf_swap_at by lia. rewrite sgn_S. ring.
Qed.

Lemma pf_expand_at k l : k < length l ->
  pf l = (sgn k * sumk (pred (length l)) (fun m =>
    sgn m * M (nth k l O) (nth m (rem_at k l) O) * pf (rem_at m (rem_at k l))))%pf.
Proof.
  intros Hk. rewrite <- (length_rem_at k l) by lia. rewrite <- pf_cons.
  rewrite pf_move_front by lia.
  transitivity ((sgn k * sgn k) * pf l)%pf; [rewrite sgn_sq; ring|ring].
Qed.


End WithM.


Lemma In_rem_at {A} k (l : list A) a : In a (rem_at k l) -> In a l.
Proof.
  revert k. induction l as [|x r IH]; intros k H; [destruct k; simpl in H; exact H|].
  destruct k as [|k]; simpl in *; [right; exact H|].
  destruct H as [H|H]; [left; exact H|right; eapply IH; exact H].
Qed.

Lemma In_rem_at_other {A} k (l : list A) a :
  k < length l -> In a l -> a <> nth k l a -> In a (rem_at k l).
Proof.
  revert k. induction l as [|x r IH]; intros k Hk H Hne; simpl in Hk; [lia|].
  destruct k as [|k]; simpl in *.
  - destruct H as [H|H]; [subst; contradiction|exact H].
  - destruct H as [H|H]; [left; exact H|right; apply IH; [lia|exact H|exact Hne]].
Qed.

Lemma NoDup_rem_at_notin k (l : list nat) :
  NoDup l -> k < length l -> ~ In (nth k l O) (rem_at k l).
Proof.
  revert k. induction l as [|x r IH]; intros k Hnd Hk; simpl in Hk; [lia|].
  inversion Hnd as [|? ? Hx Hr]; subst.
  destruct k as [|k]; simpl.
  - exact Hx.
  - intros [H|H].
    + apply Hx. rewrite H. apply nth_In. lia.
    + apply (IH k Hr ltac:(lia)). exact H.
Qed.

Lemma pf_ext M N l : (forall a b, In a l -> In b l -> M a b = N a b) -> pf M l = pf N l.
Proof.
  remember (length l) as n eqn:En. revert l En.
  induction n as [n IH] using (well_founded_induction lt_wf). intros l En H.
  destruct l as [|x r]; [reflexivity|]. rewrite !pf_cons. apply sumk_ext. intros k Hk.
  rewrite (H x (nth k r O)) by (try (left; reflexivity); right; apply nth_In; exact Hk).
  rewrite (IH (length (rem_at k r))); [reflexivity| simpl in En; rewrite length_rem_at by lia; lia | reflexivity |].
  intros a b Ha Hb. apply H; right; eapply In_rem_at; eassumption.
Qed.

Definition skew (M : nat -> nat -> D.t) : Prop := forall a b, M a b = D.opp (M b a).

Section TwoRegular.
Hypothesis two_reg : forall a : D.t, D.add a a = D.zero -> a = D.zero.

Lemma skew_diag M a : skew M -> M a a = D.zero.
Proof. intros Sk. apply two_reg. rewrite (Sk a a) at 1. ring. Qed.

Lemma pf_head_dup M x r : skew M -> pf M (x :: x :: r) = D.zero.
Proof.
  intros Sk. apply two_reg. rewrite (pf_swap_head M Sk x x r) at 1. ring.
Qed.

Lemma pf_dup M y r i : skew M -> i < length r -> nth i r O = y -> pf M (y :: r) = D.zero.
Proof.
  intros Sk Hi Hy.
  assert (E := pf_move_front M Sk (S i) (y :: r) ltac:(simpl; lia)).
  simpl nth in E. simpl rem_at in E. rewrite Hy, pf_head_dup in E by exact Sk.
  transitivity ((sgn (S i) * sgn (S i)) * pf M (y :: r))%pf; [rewrite sgn_sq; ring|].
  transitivity (sgn (S i) * (sgn (S i) * pf M (y :: r)))%pf; [ring|].
  rewrite <- E. ring.
Qed.

(** The congruence that adds alpha times index h to index x, in row and column. *)
Definition transv (M : nat -> nat -> D.t) (x h : nat) (alpha : D.t) : nat -> nat -> D.t :=
  fun a b =>
    if Nat.eqb a x then (if Nat.eqb b x then M a b else (M a b + alpha * M h b)%pf)
    else if Nat.eqb b x then (M a b - alpha * M h a)%pf else M a b.

Lemma transv_skew M x h alpha : skew M -> skew (transv M x h alpha).
Proof.
  intros Sk a b. unfold transv.
  destruct (Nat.eqb a x) eqn:Ea; destruct (Nat.eqb b x) eqn:Eb; rewrite (Sk a b); ring.
Qed.

Lemma pf_transv M x h alpha l :
  skew M -> x <> h -> NoDup l -> In x l -> In h l -> pf (transv M x h alpha) l = pf M l.
Proof.
  intros Sk Hxh Hnd Hx Hh.
  destruct (In_nth l x O Hx) as [k [Hk Ek]].
  set (r := rem_at k l).
  assert (Hxr : ~ In x r) by (subst r; rewrite <- Ek; apply NoDup_rem_at_notin; assumption).
  assert (Hhr : In h r).
  { subst r. apply In_rem_at_other; [exact Hk|exact Hh|]. rewrite (nth_indep l h O) by exact Hk. rewrite Ek. congruence. }
  destruct (In_nth r h O Hhr) as [i [Hi Ei]].
  assert (EN := pf_move_front (transv M x h alpha) (transv_skew M x h alpha Sk) k l Hk).
  assert (EM := pf_move_front M Sk k l Hk).
  rewrite Ek in EN, EM. fold r in EN, EM.
  assert (Hcons : pf (transv M x h alpha) (x :: r) = (pf M (x :: r) + alpha * pf M (h :: r))%pf).
  { rewrite !pf_cons. rewrite <- sumk_scale, <- sumk_add. apply sumk_ext. intros m Hm.
    assert (Hm_ne : nth m r O <> x) by (intro E; apply Hxr; rewrite <- E; apply nth_In; exact Hm).
    rewrite (pf_ext (transv M x h alpha) M (rem_at m r)).
    - unfold transv. rewrite Nat.eqb_refl. replace (Nat.eqb (nth m r O) x) with false
        by (symmetry; apply Nat.eqb_neq; exact Hm_ne). ring.
    - intros a b Ha Hb. unfold transv.
      replace (Nat.eqb a x) with false by (symmetry; apply Nat.eqb_neq; intro E; subst; apply Hxr; eapply In_rem_at; exact Ha).
      replace (Nat.eqb b x) with false by (symmetry; apply Nat.eqb_neq; intro E; subst; apply Hxr; eapply In_rem_at; exact Hb).
      reflexivity. }
  rewrite (pf_dup M h r i Sk Hi Ei) in Hcons.
  assert (G : (sgn k * pf (transv M x h alpha) l)%pf = (sgn k * pf M l)%pf)
    by (rewrite <- EN, <- EM, Hcons; ring).
  transitivity (sgn k * sgn k * pf (transv M x h alpha) l)%pf; [rewrite sgn_sq; ring|].
  transitivity (sgn k * sgn k * pf M l)%pf; [|rewrite sgn_sq; ring].
  replace (sgn k * sgn k * pf (transv M x h alpha) l)%pf with (sgn k * (sgn k * pf (transv M x h alpha) l))%pf by ring.
  rewrite G. ring.
Qed.

End TwoRegular.

End PfaffianTheory.

(** A field of characteristic other than 2 with decidable equality. *)
Module Type PfField.
  Include CommutativeRing.
  Parameter div : t -> t -> t.
  Parameter inv : t -> t.
  Axiom field_th : field_theory zero one add mul sub opp div inv (@eq t).
  Parameter eq_dec : forall a b : t, {a = b} + {a <> b}.
  Axiom two_nonzero : add one one <> zero.
End PfField.

Module PfaffianKernel (F : PfField).
Module P := PfaffianTheory F.
Import P.
Add Field pf_field : F.field_th.

Declare Scope pk_scope.
Delimit Scope pk_scope with pk.
Local Infix "+" := F.add : pk_scope.
Local Infix "*" := F.mul : pk_scope.
Local Infix "-" := F.sub : pk_scope.
Local Notation "- x" := (F.opp x) : pk_scope.

Lemma one_nonzero : F.one <> F.zero.
Proof. exact (F_1_neq_0 F.field_th). Qed.

Lemma two_reg : forall a : F.t, F.add a a = F.zero -> a = F.zero.
Proof.
  intros a H. assert (E : (F.mul (F.add F.one F.one) a) = F.zero) by (rewrite <- H; ring).
  destruct (F.eq_dec a F.zero) as [Z|NZ]; [exact Z|].
  exfalso. apply F.two_nonzero.
  replace (F.add F.one F.one) with (F.mul (F.mul (F.add F.one F.one) a) (F.inv a)) by (field; exact NZ).
  rewrite E. ring.
Qed.

Lemma mul_zero_l a b : F.mul a b = F.zero -> a <> F.zero -> b = F.zero.
Proof.
  intros H Ha. replace b with (F.mul (F.inv a) (F.mul a b)) by (field; exact Ha). rewrite H. ring.
Qed.

Definition lsum (l : list nat) (f : nat -> F.t) : F.t :=
  fold_right (fun a acc => F.add (f a) acc) F.zero l.

Lemma lsum_ext l f g : (forall a, In a l -> f a = g a) -> lsum l f = lsum l g.
Proof.
  induction l as [|x r IH]; intros H; simpl; [reflexivity|].
  rewrite H by (left; reflexivity). rewrite IH by (intros; apply H; right; assumption). reflexivity.
Qed.

Lemma lsum_add l f g : lsum l (fun b => (f b + g b)%pk) = (lsum l f + lsum l g)%pk.
Proof. induction l as [|x r IH]; simpl; [ring|]. rewrite IH. ring. Qed.

Lemma lsum_scale l c f : lsum l (fun b => (c * f b)%pk) = (c * lsum l f)%pk.
Proof. induction l as [|x r IH]; simpl; [ring|]. rewrite IH. ring. Qed.

Lemma lsum_zero l f : (forall a, In a l -> f a = F.zero) -> lsum l f = F.zero.
Proof.
  induction l as [|x r IH]; intros H; simpl; [reflexivity|].
  rewrite H by (left; reflexivity). rewrite IH by (intros; apply H; right; assumption). ring.
Qed.

Lemma lsum_single l h c :
  NoDup l -> In h l -> lsum l (fun b => if Nat.eqb b h then c else F.zero) = c.
Proof.
  induction l as [|x r IH]; intros Hnd Hh; [destruct Hh|]. inversion Hnd as [|? ? Hx Hr]; subst.
  simpl. destruct (Nat.eqb x h) eqn:E.
  - apply Nat.eqb_eq in E. subst. rewrite lsum_zero; [ring|].
    intros a Ha. replace (Nat.eqb a h) with false; [reflexivity|].
    symmetry. apply Nat.eqb_neq. intro; subst; contradiction.
  - destruct Hh as [Hh|Hh]; [apply Nat.eqb_neq in E; contradiction|]. rewrite IH by assumption. ring.
Qed.

Lemma lsum_perm l l' f : Permutation l l' -> lsum l f = lsum l' f.
Proof.
  intros H. induction H; simpl; try reflexivity.
  - rewrite IHPermutation. reflexivity.
  - ring.
  - rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.

Definition ker_on (M : nat -> nat -> F.t) (l : list nat) (v : nat -> F.t) : Prop :=
  forall a, In a l -> lsum l (fun b => (M a b * v b)%pk) = F.zero.

Definition nz_on (l : list nat) (v : nat -> F.t) : Prop := exists b, In b l /\ v b <> F.zero.

Lemma ker_on_perm M l l' v : Permutation l l' -> ker_on M l v -> ker_on M l' v.
Proof.
  intros Hp H a Ha. rewrite <- (lsum_perm l l') by exact Hp. apply H.
  apply (Permutation_in a (Permutation_sym Hp)). exact Ha.
Qed.

Lemma nz_on_perm l l' v : Permutation l l' -> nz_on l v -> nz_on l' v.
Proof. intros Hp [b [Hb Hv]]. exists b. split; [apply (Permutation_in b Hp); exact Hb|exact Hv]. Qed.

Lemma lsum_sub l f g : lsum l (fun b => (f b - g b)%pk) = (lsum l f - lsum l g)%pk.
Proof. induction l as [|x r IH]; simpl; [ring|]. rewrite IH. ring. Qed.

Lemma perm_rem_at k (r : list nat) : k < length r -> Permutation r (nth k r O :: rem_at k r).
Proof.
  revert k. induction r as [|x r IH]; intros k Hk; simpl in Hk; [lia|].
  destruct k as [|k]; simpl; [apply Permutation_refl|].
  apply perm_trans with (x :: nth k r O :: rem_at k r).
  - apply perm_skip. apply IH. lia.
  - apply perm_swap.
Qed.

Lemma find_nonzero (r : list nat) (f : nat -> F.t) :
  {y | In y r /\ f y <> F.zero} + {forall y, In y r -> f y = F.zero}.
Proof.
  induction r as [|x r IH].
  - right. intros y [].
  - destruct (F.eq_dec (f x) F.zero) as [Z|NZ].
    + destruct IH as [[y [Hy Hf]]|H].
      * left. exists y. split; [right; exact Hy|exact Hf].
      * right. intros y [<-|Hy]; [exact Z|apply H; exact Hy].
    + left. exists x. split; [left; reflexivity|exact NZ].
Qed.

(** Kernel vectors of a transvected matrix give kernel vectors of the original. *)
Lemma ker_transv M x0 h alpha L u :
  skew M -> x0 <> h -> NoDup L -> In x0 L -> In h L ->
  nz_on L u -> ker_on (transv M x0 h alpha) L u ->
  exists w, nz_on L w /\ ker_on M L w.
Proof.
  intros Sk Hxh Hnd Hx Hh Hnz Hk.
  set (w := fun b => if Nat.eqb b h then (u h + alpha * u x0)%pk else u b).
  assert (Hw : forall a, lsum L (fun b => (M a b * w b)%pk) =
                         (lsum L (fun b => (M a b * u b)%pk) + alpha * u x0 * M a h)%pk).
  { intros a. rewrite <- (lsum_single L h (alpha * u x0 * M a h)%pk Hnd Hh), <- lsum_add.
    apply lsum_ext. intros b Hb. unfold w. destruct (Nat.eqb b h) eqn:E.
    - apply Nat.eqb_eq in E. subst. ring.
    - ring. }
  assert (HNo : forall a, In a L -> a <> x0 ->
    lsum L (fun b => (transv M x0 h alpha a b * u b)%pk) =
    (lsum L (fun b => (M a b * u b)%pk) - alpha * M h a * u x0)%pk).
  { intros a Ha Hax. rewrite <- (lsum_single L x0 (alpha * M h a * u x0)%pk Hnd Hx), <- lsum_sub.
    apply lsum_ext. intros b Hb. unfold transv.
    replace (Nat.eqb a x0) with false by (symmetry; apply Nat.eqb_neq; exact Hax).
    destruct (Nat.eqb b x0) eqn:E; [apply Nat.eqb_eq in E; subst; ring|ring]. }
  assert (HNx : lsum L (fun b => (transv M x0 h alpha x0 b * u b)%pk) =
    (lsum L (fun b => (M x0 b * u b)%pk) + alpha * lsum L (fun b => (M h b * u b)%pk)
     - alpha * M h x0 * u x0)%pk).
  { rewrite <- lsum_scale, <- lsum_add, <- (lsum_single L x0 (alpha * M h x0 * u x0)%pk Hnd Hx), <- lsum_sub.
    apply lsum_ext. intros b Hb. unfold transv. rewrite Nat.eqb_refl.
    destruct (Nat.eqb b x0) eqn:E; [apply Nat.eqb_eq in E; subst; ring|ring]. }
  assert (Hhh : M h h = F.zero) by (apply (skew_diag two_reg); exact Sk).
  assert (Hh0 : lsum L (fun b => (M h b * u b)%pk) = F.zero).
  { assert (E := Hk h Hh). rewrite HNo in E by (try exact Hh; congruence). rewrite Hhh in E.
    rewrite <- E. ring. }
  exists w. split.
  - destruct Hnz as [b0 [Hb0 Hu]]. destruct (Nat.eq_dec b0 h) as [->|Hne].
    + destruct (F.eq_dec (u x0) F.zero) as [Z|NZ].
      * exists h. split; [exact Hh|]. unfold w. rewrite Nat.eqb_refl, Z.
        replace (u h + alpha * F.zero)%pk with (u h) by ring. exact Hu.
      * exists x0. split; [exact Hx|]. unfold w.
        replace (Nat.eqb x0 h) with false by (symmetry; apply Nat.eqb_neq; exact Hxh). exact NZ.
    + exists b0. split; [exact Hb0|]. unfold w.
      replace (Nat.eqb b0 h) with false by (symmetry; apply Nat.eqb_neq; exact Hne). exact Hu.
  - intros a Ha. rewrite Hw. destruct (Nat.eq_dec a x0) as [->|Hax].
    + assert (E := Hk x0 Hx). rewrite HNx, Hh0 in E. rewrite (Sk x0 h). rewrite <- E. ring.
    + assert (E := Hk a Ha). rewrite HNo in E by assumption. rewrite (Sk a h). rewrite <- E. ring.
Qed.

Lemma transv_off M x0 h alpha a b : a <> x0 -> b <> x0 -> transv M x0 h alpha a b = M a b.
Proof.
  intros Ha Hb. unfold transv.
  replace (Nat.eqb a x0) with false by (symmetry; apply Nat.eqb_neq; exact Ha).
  replace (Nat.eqb b x0) with false by (symmetry; apply Nat.eqb_neq; exact Hb). reflexivity.
Qed.

Lemma transv_row M x0 h alpha b : b <> x0 -> transv M x0 h alpha x0 b = (M x0 b + alpha * M h b)%pk.
Proof.
  intros Hb. unfold transv. rewrite Nat.eqb_refl.
  replace (Nat.eqb b x0) with false by (symmetry; apply Nat.eqb_neq; exact Hb). reflexivity.
Qed.

(** Clearing the entries in columns x and y of the rows in P by congruences. *)
Lemma clear_rows x y c P : forall M, skew M -> NoDup (x :: y :: P) -> M x y = c -> c <> F.zero ->
  exists M', skew M' /\ M' x y = c /\
    (forall i, In i P -> M' i x = F.zero /\ M' i y = F.zero) /\
    (forall a b, ~ In a P -> ~ In b P -> M' a b = M a b) /\
    (forall L, NoDup L -> incl (x :: y :: P) L -> pf M' L = pf M L) /\
    (forall L u, NoDup L -> incl (x :: y :: P) L -> nz_on L u -> ker_on M' L u ->
       exists w, nz_on L w /\ ker_on M L w).
Proof.
  induction P as [|i P IH]; intros M Sk Hnd Hxy Hc.
  - exists M. split; [exact Sk|]. split; [exact Hxy|]. split; [intros i []|].
    split; [reflexivity|]. split; [reflexivity|]. intros L u _ _ Hnz Hk. exists u. split; assumption.
  - assert (Hix : i <> x) by (intro E; subst; inversion Hnd as [|? ? Hx _]; apply Hx; right; left; reflexivity).
    assert (Hiy : i <> y).
    { intro E; subst. inversion Hnd as [|? ? _ Hr]. inversion Hr as [|? ? Hy _]. apply Hy. left. reflexivity. }
    assert (Hxy' : x <> y) by (intro E; subst; inversion Hnd as [|? ? Hx _]; apply Hx; left; reflexivity).
    assert (HiP : ~ In i P).
    { inversion Hnd as [|? ? _ Hr]. inversion Hr as [|? ? _ Hr']. inversion Hr' as [|? ? HiP _]. exact HiP. }
    assert (HxP : ~ In x P) by (intro H; inversion Hnd as [|? ? Hx _]; apply Hx; right; right; exact H).
    assert (HyP : ~ In y P).
    { intro H. inversion Hnd as [|? ? _ Hr]. inversion Hr as [|? ? Hy _]. apply Hy. right. exact H. }
    set (a1 := F.div (M i x) c).
    set (N1 := transv M i y a1).
    set (b1 := F.opp (F.div (M i y) c)).
    set (N2 := transv N1 i x b1).
    assert (S1 : skew N1) by (apply transv_skew; exact Sk).
    assert (S2 : skew N2) by (apply transv_skew; exact S1).
    assert (Hyy : M y y = F.zero) by (apply (skew_diag two_reg); exact Sk).
    assert (Hxx : M x x = F.zero) by (apply (skew_diag two_reg); exact Sk).
    assert (E2x : N2 i x = F.zero).
    { unfold N2. rewrite transv_row by congruence. unfold N1. rewrite transv_row by congruence.
      rewrite transv_off by congruence. rewrite Hxx, (Sk y x), Hxy. unfold a1. field. exact Hc. }
    assert (E2y : N2 i y = F.zero).
    { unfold N2. rewrite transv_row by congruence. unfold N1. rewrite transv_row by congruence.
      rewrite transv_off by congruence. rewrite Hyy, Hxy. unfold b1. field. exact Hc. }
    assert (E2off : forall a b, a <> i -> b <> i -> N2 a b = M a b).
    { intros a b Ha Hb. unfold N2. rewrite transv_off by assumption. unfold N1. rewrite transv_off by assumption. reflexivity. }
    assert (Hnd' : NoDup (x :: y :: P)).
    { inversion Hnd as [|? ? Hx Hr]. inversion Hr as [|? ? Hy Hr']. inversion Hr' as [|? ? _ HP].
      constructor; [intros [Hz|Hz]; [apply Hx; left; exact Hz|apply Hx; right; right; exact Hz]|].
      constructor; [intros Hz; apply Hy; right; exact Hz|exact HP]. }
    destruct (IH N2 S2 Hnd' ltac:(rewrite E2off by congruence; exact Hxy) Hc)
      as [M' [SM' [Mxy [Hclr [Hoff [Hpf Hker]]]]]].
    exists M'. split; [exact SM'|]. split; [exact Mxy|]. split.
    + intros j [<-|Hj].
      * rewrite !Hoff by assumption. split; assumption.
      * apply Hclr. exact Hj.
    + split.
      * intros a b Ha Hb.
        rewrite Hoff; [| intro Hz; apply Ha; right; exact Hz | intro Hz; apply Hb; right; exact Hz].
        apply E2off; [intro E; apply Ha; left; symmetry; exact E | intro E; apply Hb; left; symmetry; exact E].
      * split.
        -- intros L HndL Hincl.
           assert (HiL : In i L) by (apply Hincl; right; right; left; reflexivity).
           assert (HxL : In x L) by (apply Hincl; left; reflexivity).
           assert (HyL : In y L) by (apply Hincl; right; left; reflexivity).
           assert (Hinc : incl (x :: y :: P) L) by (intros z Hz; apply Hincl; destruct Hz as [<-|[<-|Hz]];
             [left; reflexivity|right; left; reflexivity|right; right; right; exact Hz]).
           rewrite (Hpf L HndL Hinc).
           unfold N2. rewrite (pf_transv two_reg) by assumption.
           unfold N1. rewrite (pf_transv two_reg) by assumption. reflexivity.
        -- intros L u HndL Hincl Hnz Hk.
           assert (HiL : In i L) by (apply Hincl; right; right; left; reflexivity).
           assert (HxL : In x L) by (apply Hincl; left; reflexivity).
           assert (HyL : In y L) by (apply Hincl; right; left; reflexivity).
           assert (Hinc : incl (x :: y :: P) L) by (intros z Hz; apply Hincl; destruct Hz as [<-|[<-|Hz]];
             [left; reflexivity|right; left; reflexivity|right; right; right; exact Hz]).
           destruct (Hker L u HndL Hinc Hnz Hk) as [w1 [Hnz1 Hk1]].
           destruct (ker_transv N1 i x b1 L w1 S1 Hix HndL HiL HxL Hnz1 Hk1) as [w2 [Hnz2 Hk2]].
           exact (ker_transv M i y a1 L w2 Sk Hiy HndL HiL HyL Hnz2 Hk2).
Qed.

(** A skew matrix on an even list of distinct indices with Pfaffian 0 has a kernel vector. *)
Theorem pf_zero_kernel : forall n l M, length l = n -> Nat.even n = true -> skew M -> NoDup l ->
  pf M l = F.zero -> exists v, nz_on l v /\ ker_on M l v.
Proof.
  intros n. induction n as [n IH] using (well_founded_induction lt_wf).
  intros l M Hlen Hev Sk Hnd Hpf.
  destruct l as [|x r].
  - exfalso. apply one_nonzero. exact Hpf.
  - destruct r as [|r0 r1].
    + simpl in Hlen. subst n. discriminate.
    + set (r := r0 :: r1). fold r in Hnd, Hpf, Hlen.
      destruct (find_nonzero r (M x)) as [[y [Hyr Hxy]]|Hzero].
      * destruct (In_nth r y O Hyr) as [k [Hk Ek]].
        set (r' := rem_at k r).
        assert (Hperm : Permutation (x :: r) (x :: y :: r')).
        { apply perm_skip. rewrite <- Ek. apply perm_rem_at. exact Hk. }
        assert (Hnd2 : NoDup (x :: y :: r')) by (eapply Permutation_NoDup; [exact Hperm|exact Hnd]).
        assert (Hpf2 : pf M (x :: y :: r') = F.zero).
        { assert (E := pf_move_front M Sk (S k) (x :: r) (proj1 (Nat.succ_lt_mono _ _) Hk)).
          change (nth (S k) (x :: r) O) with (nth k r O) in E.
          change (rem_at (S k) (x :: r)) with (x :: rem_at k r) in E. rewrite Ek in E. fold r' in E.
          rewrite Hpf in E. rewrite (pf_swap_head M Sk x y r') in E.
          replace (pf M (x :: y :: r')) with (F.opp (F.opp (pf M (x :: y :: r')))) by ring.
          rewrite E. ring. }
        destruct (clear_rows x y (M x y) r' M Sk Hnd2 eq_refl Hxy)
          as [M' [SM' [Mxy [Hclr [_ [Hpfc Hkerc]]]]]].
        assert (Hpf3 : pf M' r' = F.zero).
        { assert (E := Hpfc (x :: y :: r') Hnd2 (incl_refl _)). rewrite Hpf2 in E.
          rewrite (pf_two M' x y r') in E.
          assert (Hd : dbl M' x y r' = F.zero).
          { unfold dbl. apply sumk_zero. intros j Hj. apply sumk_zero. intros p Hp.
            destruct (Nat.eqb p j); [reflexivity|].
            assert (Hin : In (nth j r' O) r') by (apply nth_In; exact Hj).
            rewrite (SM' x (nth j r' O)). rewrite (proj1 (Hclr _ Hin)). ring. }
          rewrite Hd, Mxy in E. apply (mul_zero_l (M x y)); [|exact Hxy].
          replace (M x y * pf M' r')%pk with ((M x y * pf M' r') + F.zero)%pk by ring. exact E. }
        assert (Hlen' : length r' = (n - 2)%nat).
        { subst r'. rewrite length_rem_at by exact Hk. simpl in Hlen. subst r. simpl. simpl in Hlen. lia. }
        assert (Hnd' : NoDup r') by (inversion Hnd2 as [|? ? _ H2]; inversion H2 as [|? ? _ H3]; exact H3).
        destruct (IH (n - 2)%nat ltac:(simpl in Hlen; lia) r' M' Hlen'
                   ltac:(replace n with (S (S (n - 2))) in Hev by (simpl in Hlen; lia); exact Hev)
                   SM' Hnd' Hpf3) as [u' [Hnz' Hk']].
        set (u := fun b => if orb (Nat.eqb b x) (Nat.eqb b y) then F.zero else u' b).
        assert (Hxr' : ~ In x r') by (inversion Hnd2 as [|? ? Hx _]; intro Hz; apply Hx; right; exact Hz).
        assert (Hyr' : ~ In y r') by (inversion Hnd2 as [|? ? _ H2]; inversion H2 as [|? ? Hy _]; exact Hy).
        assert (Hu : forall b, In b r' -> u b = u' b).
        { intros b Hb. unfold u.
          replace (Nat.eqb b x) with false by (symmetry; apply Nat.eqb_neq; intro E; subst; contradiction).
          replace (Nat.eqb b y) with false by (symmetry; apply Nat.eqb_neq; intro E; subst; contradiction).
          reflexivity. }
        assert (Hsum : forall a, lsum (x :: y :: r') (fun b => (M' a b * u b)%pk) =
                                 lsum r' (fun b => (M' a b * u' b)%pk)).
        { intros a. simpl. unfold u at 1 2. rewrite Nat.eqb_refl. simpl.
          replace (Nat.eqb y x) with false by (symmetry; apply Nat.eqb_neq; intro E; subst; inversion Hnd2 as [|? ? Hx _]; apply Hx; left; reflexivity).
          rewrite Nat.eqb_refl. simpl.
          rewrite (lsum_ext r' (fun b => (M' a b * u b)%pk) (fun b => (M' a b * u' b)%pk)) by (intros b Hb; rewrite Hu by exact Hb; reflexivity).
          ring. }
        assert (Hnzu : nz_on (x :: y :: r') u).
        { destruct Hnz' as [b [Hb Hv]]. exists b. split; [right; right; exact Hb|]. rewrite Hu by exact Hb. exact Hv. }
        assert (Hku : ker_on M' (x :: y :: r') u).
        { intros a Ha. rewrite Hsum. destruct Ha as [<-|[<-|Ha]].
          - apply lsum_zero. intros b Hb. rewrite (SM' x b), (proj1 (Hclr b Hb)). ring.
          - apply lsum_zero. intros b Hb. rewrite (SM' y b), (proj2 (Hclr b Hb)). ring.
          - apply Hk'. exact Ha. }
        destruct (Hkerc (x :: y :: r') u Hnd2 (incl_refl _) Hnzu Hku) as [w [Hnzw Hkw]].
        exists w. split.
        -- eapply nz_on_perm; [apply Permutation_sym; exact Hperm|exact Hnzw].
        -- eapply ker_on_perm; [apply Permutation_sym; exact Hperm|exact Hkw].
      * set (v := fun b => if Nat.eqb b x then F.one else F.zero).
        exists v. split.
        -- exists x. split; [left; reflexivity|]. unfold v. rewrite Nat.eqb_refl. exact one_nonzero.
        -- intros a Ha. rewrite (lsum_ext _ _ (fun b => if Nat.eqb b x then M a x else F.zero)).
           ++ rewrite lsum_single by (try exact Hnd; left; reflexivity).
              destruct Ha as [<-|Ha]; [apply (skew_diag two_reg); exact Sk|].
              rewrite (Sk a x), (Hzero a Ha). ring.
           ++ intros b Hb. unfold v. destruct (Nat.eqb b x) eqn:E; [apply Nat.eqb_eq in E; subst; ring|ring].
Qed.

End PfaffianKernel.
