(** Census of the Cayley-Dickson associator phases by ANF degree. anf_degree
    computes the degree of a truth table on x < 2^k as the largest monomial
    weight carrying a nonzero ANF coefficient, and census k d counts the
    unordered pairs 0 < p < q < 2^k whose phase assoc k p q has
    anf_degree d. By assoc_degree_is that degree is max(1, log2 q - 1), so
    the count runs over the bit-length shells 2^b <= q < 2^(b+1): for
    k >= 3 there are 21 pairs of degree 1 (every pair inside the octonion
    level), 3 2^d (2^(d+1) - 1) pairs of degree d for 2 <= d <= k - 2, and
    none of any other degree, so the degree-d count does not depend on k
    and the counts over all degrees add up to (2^k - 1)(2^k - 2)/2. *)

From Stdlib Require Import Arith ZArith Lia.
Require Import CdImaginarySumConference CdTowerBasisSign CdSignRowAnf CdAssociatorAnf.
Open Scope nat_scope.

(** The largest weight among the monomials s < n with nonzero coefficient. *)
Fixpoint max_weight (k : nat) (f : nat -> bool) (n : nat) : nat :=
  match n with
  | O => O
  | S m => Nat.max (max_weight k f m) (if anf_coef k f m then weight k m else O)
  end.

Definition anf_degree (k : nat) (f : nat -> bool) : nat := max_weight k f (Nat.pow 2 k).

Lemma max_weight_le k f d : forall n, n <= Nat.pow 2 k ->
  (forall s, s < Nat.pow 2 k -> anf_coef k f s = true -> weight k s <= d) -> max_weight k f n <= d.
Proof.
  induction n as [|m IH]; intros Hn B; simpl; [lia|]. apply Nat.max_lub; [apply IH; [lia|exact B]|].
  destruct (anf_coef k f m) eqn:C; [apply B; [lia|exact C]|lia].
Qed.

Lemma max_weight_ge k f s : forall n, s < n -> anf_coef k f s = true -> weight k s <= max_weight k f n.
Proof.
  induction n as [|m IH]; intros Hs C; simpl; [lia|].
  destruct (Nat.eq_dec s m) as [->|Hne]; [rewrite C; apply Nat.le_max_r|].
  eapply Nat.le_trans; [apply IH; [lia|exact C]|apply Nat.le_max_l].
Qed.

(** degree_is pins the computed degree. *)
Lemma degree_is_anf k f d : degree_is k f d -> anf_degree k f = d.
Proof.
  intros [B [s [Hs [W C]]]]. unfold anf_degree. apply Nat.le_antisymm.
  - apply max_weight_le; [lia|exact B].
  - rewrite <- W. apply max_weight_ge; assumption.
Qed.

Lemma degree_is_unique k f d e : degree_is k f d -> degree_is k f e -> d = e.
Proof. intros D E. rewrite <- (degree_is_anf k f d D). apply degree_is_anf, E. Qed.

Lemma assoc_anf_degree k p q : 3 <= k -> 0 < p -> p < q -> q < Nat.pow 2 k ->
  anf_degree k (assoc k p q) = Nat.max 1 (Nat.log2 q - 1).
Proof.
  intros Hk Hp Hpq Hq. rewrite (degree_is_anf k _ (assoc_degree p q)) by (apply assoc_degree_is; lia).
  unfold assoc_degree. rewrite (Nat.max_r p q) by lia. reflexivity.
Qed.

Fixpoint sum_below (n : nat) (f : nat -> nat) : nat :=
  match n with
  | O => O
  | S m => sum_below m f + f m
  end.

(** Unordered pairs 0 < p < q < 2^k whose associator phase has ANF degree d. *)
Definition census (k d : nat) : nat :=
  sum_below (Nat.pow 2 k)
    (fun q => sum_below q (fun p => if Nat.eqb p 0 then 0 else Nat.b2n (Nat.eqb (anf_degree k (assoc k p q)) d))).

Lemma sum_ext n f g : (forall i, i < n -> f i = g i) -> sum_below n f = sum_below n g.
Proof. induction n as [|m IH]; intro E; simpl; [reflexivity|]. rewrite IH, E by (lia || (intros; apply E; lia)). reflexivity. Qed.

Lemma sum_zero n f : (forall i, i < n -> f i = 0) -> sum_below n f = 0.
Proof. induction n as [|m IH]; intro E; simpl; [reflexivity|]. rewrite IH, E by (lia || (intros; apply E; lia)). reflexivity. Qed.

Lemma sum_add n f g : sum_below n (fun i => f i + g i) = sum_below n f + sum_below n g.
Proof. induction n as [|m IH]; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Lemma sum_split a b f : sum_below (a + b) f = sum_below a f + sum_below b (fun i => f (a + i)).
Proof. induction b as [|m IH]; simpl; [rewrite Nat.add_0_r; lia|]. rewrite Nat.add_succ_r. simpl. rewrite IH. lia. Qed.

Lemma sum_swap n m f : sum_below n (fun i => sum_below m (f i)) = sum_below m (fun j => sum_below n (fun i => f i j)).
Proof.
  induction n as [|n IH]; simpl; [symmetry; apply sum_zero; reflexivity|]. rewrite IH, <- sum_add. reflexivity.
Qed.

(** Gauss: twice the sum of i < n is n (n - 1). *)
Lemma sum_id n : 2 * sum_below n (fun i => i) = n * (n - 1).
Proof. induction n as [|m IH]; simpl sum_below; [reflexivity|]. rewrite Nat.mul_add_distr_l, IH. destruct m; simpl; nia. Qed.

(** One nonzero p < q per pair in the inner sum when the predicate depends on q only. *)
Lemma inner_const q c : sum_below q (fun p => if Nat.eqb p 0 then 0 else c) = (q - 1) * c.
Proof.
  induction q as [|m IH]; simpl; [reflexivity|]. rewrite IH.
  destruct (Nat.eqb_spec m 0) as [->|Hm]; simpl; [lia|]. destruct m; [lia|]. simpl. nia.
Qed.

Definition shell_weight (q : nat) : nat := q - 1.

Lemma census_shells k d : 3 <= k ->
  census k d = sum_below (Nat.pow 2 k) (fun q => shell_weight q * Nat.b2n (Nat.eqb (Nat.max 1 (Nat.log2 q - 1)) d)).
Proof.
  intro Hk. unfold census. apply sum_ext. intros q Hq. unfold shell_weight. rewrite <- inner_const.
  apply sum_ext. intros p Hp. destruct (Nat.eqb_spec p 0) as [->|Hp0]; [reflexivity|].
  rewrite assoc_anf_degree by lia. reflexivity.
Qed.

Lemma log2_low b q : 1 <= b -> q < Nat.pow 2 b -> Nat.log2 q < b.
Proof.
  intros Hb Hq. destruct (Nat.eq_dec q 0) as [->|Hq0]; [change (Nat.log2 0) with 0; lia|]. apply (proj1 (Nat.log2_lt_pow2 q b ltac:(lia))), Hq.
Qed.

Lemma log2_shell b i : i < Nat.pow 2 b -> Nat.log2 (Nat.pow 2 b + i) = b.
Proof. intro Hi. apply Nat.log2_unique; [lia|]. simpl. lia. Qed.

(** Restricting a sum over q < 2^k to the shell log2 q = b. *)
Lemma sum_shell b f : 1 <= b -> forall k, b < k ->
  sum_below (Nat.pow 2 k) (fun q => if Nat.eqb (Nat.log2 q) b then f q else 0) =
  sum_below (Nat.pow 2 b) (fun i => f (Nat.pow 2 b + i)).
Proof.
  intros Hb k Hk. induction k as [|k IH]; [lia|].
  replace (Nat.pow 2 (S k)) with (Nat.pow 2 k + Nat.pow 2 k) by (simpl; lia). rewrite sum_split.
  destruct (Nat.eq_dec b k) as [<-|Hne].
  - rewrite sum_zero, Nat.add_0_l.
    + apply sum_ext. intros i Hi. rewrite log2_shell, Nat.eqb_refl by exact Hi. reflexivity.
    + intros q Hq. pose proof (log2_low b q Hb Hq). destruct (Nat.eqb_spec (Nat.log2 q) b); [lia|reflexivity].
  - rewrite IH by lia. rewrite (sum_zero (Nat.pow 2 k)); [lia|].
    intros i Hi. rewrite log2_shell by exact Hi. destruct (Nat.eqb_spec k b); [lia|reflexivity].
Qed.

(** Restricting a sum over q < 2^k to log2 q < c for c <= k, read as q < 2^c. *)
Lemma sum_prefix c f : 1 <= c -> forall k, c <= k ->
  sum_below (Nat.pow 2 k) (fun q => if Nat.ltb (Nat.log2 q) c then f q else 0) = sum_below (Nat.pow 2 c) f.
Proof.
  intros Hc k Hk. induction k as [|k IH]; [lia|].
  destruct (Nat.eq_dec c (S k)) as [<-|Hne].
  - apply sum_ext. intros q Hq. pose proof (log2_low c q Hc Hq). destruct (Nat.ltb_spec (Nat.log2 q) c); lia.
  - replace (Nat.pow 2 (S k)) with (Nat.pow 2 k + Nat.pow 2 k) by (simpl; lia). rewrite sum_split, IH by lia.
    rewrite (sum_zero (Nat.pow 2 k)); [lia|].
    intros i Hi. rewrite log2_shell by exact Hi. destruct (Nat.ltb_spec k c); [lia|reflexivity].
Qed.

(** The pairs that the bit-length shell 2^b <= q < 2^(b+1) adds, b >= 1. *)
Lemma shell_count b : 1 <= b ->
  sum_below (Nat.pow 2 b) (fun i => shell_weight (Nat.pow 2 b + i)) = 3 * Nat.pow 2 (b - 1) * (Nat.pow 2 b - 1).
Proof.
  intro Hb. unfold shell_weight. destruct b as [|c]; [lia|]. simpl Nat.sub. rewrite Nat.sub_0_r.
  replace (Nat.pow 2 (S c)) with (2 * Nat.pow 2 c) by (simpl; lia).
  pose proof (Nat.pow_nonzero 2 c ltac:(lia)) as H.
  rewrite (sum_ext _ _ (fun i => (2 * Nat.pow 2 c - 1) + i)) by (intros; lia).
  rewrite sum_add. pose proof (sum_id (2 * Nat.pow 2 c)) as G.
  assert (forall n x, sum_below n (fun _ => x) = n * x) as Kc by (induction n; intros; simpl; [|rewrite IHn]; lia).
  rewrite Kc. remember (Nat.pow 2 c) as M. remember (sum_below (2 * M) (fun i => i)) as T. nia.
Qed.

(** Every pair inside the octonion level has degree 1. *)
Theorem census_degree_one k : 3 <= k -> census k 1 = 21.
Proof.
  intro Hk. rewrite census_shells by exact Hk.
  rewrite (sum_ext _ _ (fun q => if Nat.ltb (Nat.log2 q) 3 then shell_weight q else 0)).
  - rewrite sum_prefix by lia. reflexivity.
  - intros q _. destruct (Nat.ltb_spec (Nat.log2 q) 3); destruct (Nat.eqb_spec (Nat.max 1 (Nat.log2 q - 1)) 1); simpl Nat.b2n; lia.
Qed.

(** For 2 <= d <= k - 2 the degree-d pairs are those of the shell log2 q = d + 1. *)
Theorem census_degree k d : 3 <= k -> 2 <= d -> d + 2 <= k -> census k d = 3 * Nat.pow 2 d * (Nat.pow 2 (d + 1) - 1).
Proof.
  intros Hk Hd Hdk. rewrite census_shells by exact Hk.
  rewrite (sum_ext _ _ (fun q => if Nat.eqb (Nat.log2 q) (d + 1) then shell_weight q else 0)).
  - rewrite sum_shell, shell_count by lia. replace (d + 1 - 1) with d by lia. reflexivity.
  - intros q _. destruct (Nat.eqb_spec (Nat.log2 q) (d + 1)); destruct (Nat.eqb_spec (Nat.max 1 (Nat.log2 q - 1)) d); simpl Nat.b2n; lia.
Qed.

(** No pair has degree 0 or degree above k - 2. *)
Theorem census_degree_none k d : 3 <= k -> (d = 0 \/ k - 2 < d) -> census k d = 0.
Proof.
  intros Hk Hd. rewrite census_shells by exact Hk. apply sum_zero. intros q Hq.
  pose proof (log2_low k q ltac:(lia) Hq).
  destruct (Nat.eqb_spec (Nat.max 1 (Nat.log2 q - 1)) d); simpl Nat.b2n; lia.
Qed.

(** Level n adds 3 2^(n-2) (2^(n-1) - 1) pairs, all of degree n - 2. *)
Corollary census_new_level n : 4 <= n -> census n (n - 2) = 3 * Nat.pow 2 (n - 2) * (Nat.pow 2 (n - 1) - 1).
Proof. intro Hn. rewrite census_degree by lia. replace (n - 2 + 1) with (n - 1) by lia. reflexivity. Qed.

(** The degree-d count is the same at every level k >= d + 2. *)
Corollary census_stable k d : 3 <= k -> d + 2 <= k -> census (S k) d = census k d.
Proof.
  intros Hk Hdk. destruct (Nat.eq_dec d 0) as [->|H0]; [rewrite !census_degree_none by lia; reflexivity|].
  destruct (Nat.eq_dec d 1) as [->|H1]; [rewrite !census_degree_one by lia; reflexivity|].
  rewrite !census_degree by lia. reflexivity.
Qed.

(** Every unordered pair of distinct nonzero indices is counted at exactly one degree:
    twice the sum over d < k is (2^k - 1)(2^k - 2). *)
Theorem census_total k : 3 <= k -> 2 * sum_below k (census k) = (Nat.pow 2 k - 1) * (Nat.pow 2 k - 2).
Proof.
  intro Hk. rewrite (sum_ext _ _ (fun d =>
    sum_below (Nat.pow 2 k) (fun q => shell_weight q * Nat.b2n (Nat.eqb (Nat.max 1 (Nat.log2 q - 1)) d))))
    by (intros; apply census_shells; exact Hk).
  rewrite sum_swap.
  rewrite (sum_ext _ _ shell_weight).
  - unfold shell_weight. pose proof (Nat.pow_nonzero 2 k ltac:(lia)) as H. remember (Nat.pow 2 k) as N.
    clear HeqN Hk. induction N as [|N IH]; [lia|]. destruct N as [|N]; [reflexivity|].
    simpl sum_below in *. rewrite Nat.mul_add_distr_l, IH by lia. destruct N; simpl; nia.
  - intros q Hq. pose proof (log2_low k q ltac:(lia) Hq) as L.
    assert (forall n e, e < n -> sum_below n (fun d => shell_weight q * Nat.b2n (Nat.eqb e d)) = shell_weight q) as One.
    { induction n as [|n IH]; intros e He; [lia|]. simpl.
      destruct (Nat.eq_dec e n) as [->|Hne].
      - rewrite Nat.eqb_refl, sum_zero; [simpl; lia|]. intros i Hi. destruct (Nat.eqb_spec n i); [lia|]. simpl. lia.
      - rewrite IH by lia. destruct (Nat.eqb_spec e n); [lia|]. simpl. lia. }
    apply One. lia.
Qed.

(** The counts that dims 8 to 256 add, read as integers. *)
Corollary census_dim256 :
  Z.of_nat (census 8 1) = 21%Z /\ Z.of_nat (census 8 2) = 84%Z /\ Z.of_nat (census 8 3) = 360%Z /\
  Z.of_nat (census 8 4) = 1488%Z /\ Z.of_nat (census 8 5) = 6048%Z /\ Z.of_nat (census 8 6) = 24384%Z.
Proof.
  rewrite census_degree_one by lia.
  rewrite (census_degree 8 2), (census_degree 8 3), (census_degree 8 4), (census_degree 8 5), (census_degree 8 6)
    by lia.
  repeat split; reflexivity.
Qed.
