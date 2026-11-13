(** Proposition 5 of docs/notes/cd_phase_degree.md, at every level.
    For n >= 3 and m < 2^(n-2), take i = 2^(n-1) + m and
    j = i + 2^(n-2).  Writing z for x mod 2^(n-2), the associator
    phase is x_(n-1) XOR [z = m] when m is nonzero and [z <> 0]
    when m is zero.  In particular, bit n-2 is absent.

    The proof uses two applications of the already proved associator
    recursion, not a finite truth-table computation.  The final degree
    statement follows from CdAssociatorAnf's all-level degree theorem. *)

From Stdlib Require Import Arith Lia Btauto.
Require Import CdImaginarySumConference CdTowerBasisSign CdSignRowAnf CdAssociatorAnf.
Open Scope nat_scope.

(** The first doubling, for the pair (m, m + 2^k), on either input half. *)
Lemma point_pair_lower_low k m z : m < Nat.pow 2 k -> z < Nat.pow 2 k ->
  assoc (S k) m (m + Nat.pow 2 k) z =
  xorb (negb (Nat.eqb m 0)) (xorb (Nat.eqb z 0) (Nat.eqb z m)).
Proof.
  intros Hm Hz. rewrite assoc_lh_low by assumption.
  rewrite (assoc_degenerate k m m z) by (try assumption; auto).
  rewrite !alt_delta, !eqb_lxor, Nat.lxor_0_r, Nat.lxor_nilpotent, Nat.eqb_refl.
  btauto.
Qed.

Lemma point_pair_lower_high k m z : m < Nat.pow 2 k -> z < Nat.pow 2 k ->
  assoc (S k) m (m + Nat.pow 2 k) (z + Nat.pow 2 k) =
  xorb (negb (Nat.eqb m 0)) (xorb (Nat.eqb z 0) (Nat.eqb z m)).
Proof.
  intros Hm Hz. rewrite assoc_high_lh, point_pair_lower_low by assumption.
  unfold cst. rewrite Nat.lxor_nilpotent, Nat.eqb_refl. btauto.
Qed.

(** The second doubling adds 1 XOR [y = 0] XOR [y = 2^k]. *)
Lemma point_pair_upper_correction k m y : m < Nat.pow 2 k -> y < Nat.pow 2 (S k) ->
  assoc (S (S k)) (m + Nat.pow 2 (S k)) (m + Nat.pow 2 k + Nat.pow 2 (S k)) y =
  xorb (assoc (S k) m (m + Nat.pow 2 k) y)
    (negb (xorb (Nat.eqb y 0) (Nat.eqb y (Nat.pow 2 k)))).
Proof.
  intros Hm Hy. pose proof (Nat.pow_nonzero 2 k ltac:(lia)) as Hpow.
  assert (Hm' : m < Nat.pow 2 (S k)) by (simpl; lia).
  assert (Hq : m + Nat.pow 2 k < Nat.pow 2 (S k)) by (simpl; lia).
  assert (Hxor : Nat.lxor (m + Nat.pow 2 k) m = Nat.pow 2 k).
  { rewrite lxor_high_l, Nat.lxor_nilpotent by assumption. reflexivity. }
  assert (Hq0 : Nat.eqb (m + Nat.pow 2 k) 0 = false) by (apply Nat.eqb_neq; lia).
  assert (Hqm : Nat.eqb (m + Nat.pow 2 k) m = false) by (apply Nat.eqb_neq; lia).
  rewrite assoc_hh_low by assumption.
  rewrite !alt_delta, !eqb_lxor, !Nat.lxor_0_r, Hxor, Hq0, Hqm. btauto.
Qed.

Lemma point_pair_low_low k m z : m < Nat.pow 2 k -> z < Nat.pow 2 k ->
  assoc (S (S k)) (m + Nat.pow 2 (S k)) (m + Nat.pow 2 k + Nat.pow 2 (S k)) z =
  xorb (Nat.eqb m 0) (Nat.eqb z m).
Proof.
  intros Hm Hz. pose proof (Nat.pow_nonzero 2 k ltac:(lia)) as Hpow.
  rewrite point_pair_upper_correction by (try assumption; simpl; lia).
  rewrite point_pair_lower_low by assumption.
  assert (Hzp : Nat.eqb z (Nat.pow 2 k) = false) by (apply Nat.eqb_neq; lia).
  rewrite Hzp. btauto.
Qed.

Lemma point_pair_low_high k m z : m < Nat.pow 2 k -> z < Nat.pow 2 k ->
  assoc (S (S k)) (m + Nat.pow 2 (S k)) (m + Nat.pow 2 k + Nat.pow 2 (S k))
    (z + Nat.pow 2 k) = xorb (Nat.eqb m 0) (Nat.eqb z m).
Proof.
  intros Hm Hz. pose proof (Nat.pow_nonzero 2 k ltac:(lia)) as Hpow.
  rewrite point_pair_upper_correction by (try assumption; simpl; lia).
  rewrite point_pair_lower_high by assumption.
  assert (Hz0 : Nat.eqb (z + Nat.pow 2 k) 0 = false) by (apply Nat.eqb_neq; lia).
  assert (Hzp : Nat.eqb (z + Nat.pow 2 k) (Nat.pow 2 k) = Nat.eqb z 0).
  { destruct (Nat.eqb_spec z 0) as [->|Hnz]; [rewrite Nat.add_0_l, Nat.eqb_refl; reflexivity|].
    apply Nat.eqb_neq. lia. }
  rewrite Hz0, Hzp. btauto.
Qed.

Lemma point_pair_top_constant k m : m < Nat.pow 2 k ->
  cst m (m + Nat.pow 2 k) = negb (Nat.eqb m 0).
Proof.
  intro Hm. pose proof (Nat.pow_nonzero 2 k ltac:(lia)) as Hpow.
  unfold cst. rewrite lxor_high_r, Nat.lxor_nilpotent, Nat.add_0_l by assumption.
  assert (Hq0 : Nat.eqb (m + Nat.pow 2 k) 0 = false) by (apply Nat.eqb_neq; lia).
  assert (Hp0 : Nat.eqb (Nat.pow 2 k) 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite Hq0, Hp0. btauto.
Qed.

(** Reduction modulo 2^k makes the missing middle bit explicit. *)
Lemma point_pair_low k m y : m < Nat.pow 2 k -> y < Nat.pow 2 (S k) ->
  assoc (S (S k)) (m + Nat.pow 2 (S k)) (m + Nat.pow 2 k + Nat.pow 2 (S k)) y =
  xorb (Nat.eqb m 0) (Nat.eqb (y mod Nat.pow 2 k) m).
Proof.
  intros Hm Hy. pose proof (Nat.pow_nonzero 2 k ltac:(lia)) as Hpow.
  destruct (Nat.ltb_spec y (Nat.pow 2 k)) as [Hlow|Hhigh].
  - rewrite point_pair_low_low, Nat.mod_small by assumption. reflexivity.
  - destruct (split_high k y Hy Hhigh) as [z [Hz ->]].
    rewrite point_pair_low_high by assumption.
    rewrite Nat.Div0.add_mod, Nat.Div0.mod_same, Nat.add_0_r, Nat.Div0.mod_mod, Nat.mod_small by lia.
    reflexivity.
Qed.

(** A uniform Boolean formula, before splitting m = 0 from m <> 0. *)
Theorem point_pair_formula k m x : m < Nat.pow 2 k -> x < Nat.pow 2 (S (S k)) ->
  assoc (S (S k)) (m + Nat.pow 2 (S k)) (m + Nat.pow 2 k + Nat.pow 2 (S k)) x =
  xorb (Nat.eqb m 0)
    (xorb (Nat.eqb (x mod Nat.pow 2 k) m)
      (andb (Nat.testbit x (S k)) (negb (Nat.eqb m 0)))).
Proof.
  intros Hm Hx. pose proof (Nat.pow_nonzero 2 k ltac:(lia)) as Hpow.
  assert (Hm' : m < Nat.pow 2 (S k)) by (simpl; lia).
  assert (Hq : m + Nat.pow 2 k < Nat.pow 2 (S k)) by (simpl; lia).
  destruct (Nat.ltb_spec x (Nat.pow 2 (S k))) as [Hlow|Hhigh].
  - rewrite point_pair_low by assumption.
    rewrite (bits_high (S k) x (S k)) by lia. btauto.
  - destruct (split_high (S k) x Hx Hhigh) as [y [Hy ->]].
    rewrite assoc_high_hh, point_pair_low, point_pair_top_constant by assumption.
    rewrite testbit_high_top by assumption.
    replace ((y + Nat.pow 2 (S k)) mod Nat.pow 2 k) with (y mod Nat.pow 2 k).
    + btauto.
    + replace (y + Nat.pow 2 (S k)) with (y + 2 * Nat.pow 2 k) by (simpl; lia).
      symmetry. apply Nat.Div0.mod_add.
Qed.

(** Proposition 5, with exactly the indices and low-bit coordinate of the note. *)
Theorem point_indicator_pairs n m x : 3 <= n -> m < Nat.pow 2 (n - 2) -> x < Nat.pow 2 n ->
  assoc n (Nat.pow 2 (n - 1) + m) (Nat.pow 2 (n - 1) + m + Nat.pow 2 (n - 2)) x =
  if Nat.eqb m 0 then negb (Nat.eqb (x mod Nat.pow 2 (n - 2)) 0)
  else xorb (Nat.testbit x (n - 1)) (Nat.eqb (x mod Nat.pow 2 (n - 2)) m).
Proof.
  destruct n as [|[|k]]; intros Hn Hm Hx; [lia|lia|].
  replace (S (S k) - 1) with (S k) by lia.
  replace (S (S k) - 2) with k in * by lia.
  replace (Nat.pow 2 (S k) + m) with (m + Nat.pow 2 (S k)) by lia.
  replace (m + Nat.pow 2 (S k) + Nat.pow 2 k) with (m + Nat.pow 2 k + Nat.pow 2 (S k)) by lia.
  rewrite point_pair_formula by assumption.
  destruct (Nat.eqb m 0) eqn:E; [apply Nat.eqb_eq in E; subst m|]; btauto.
Qed.

Corollary point_indicator_nonzero n m x :
  3 <= n -> m < Nat.pow 2 (n - 2) -> m <> 0 -> x < Nat.pow 2 n ->
  assoc n (Nat.pow 2 (n - 1) + m) (Nat.pow 2 (n - 1) + m + Nat.pow 2 (n - 2)) x =
  xorb (Nat.testbit x (n - 1)) (Nat.eqb (x mod Nat.pow 2 (n - 2)) m).
Proof.
  intros Hn Hm Hnz Hx. rewrite point_indicator_pairs by assumption.
  rewrite (proj2 (Nat.eqb_neq m 0) Hnz). reflexivity.
Qed.

Corollary point_indicator_zero n x : 3 <= n -> x < Nat.pow 2 n ->
  assoc n (Nat.pow 2 (n - 1)) (Nat.pow 2 (n - 1) + Nat.pow 2 (n - 2)) x =
  negb (Nat.eqb (x mod Nat.pow 2 (n - 2)) 0).
Proof.
  intros Hn Hx. pose proof (Nat.pow_nonzero 2 (n - 2) ltac:(lia)) as Hpow.
  pose proof (point_indicator_pairs n 0 x Hn ltac:(lia) Hx) as H.
  rewrite Nat.add_0_r in H. exact H.
Qed.

(** The family really occupies the top degree stratum for every n >= 3. *)
Corollary point_indicator_degree n m : 3 <= n -> m < Nat.pow 2 (n - 2) ->
  degree_is n
    (assoc n (Nat.pow 2 (n - 1) + m) (Nat.pow 2 (n - 1) + m + Nat.pow 2 (n - 2))) (n - 2).
Proof.
  destruct n as [|[|k]]; intros Hn Hm; [lia|lia|].
  replace (S (S k) - 1) with (S k) by lia.
  replace (S (S k) - 2) with k in * by lia.
  pose proof (Nat.pow_nonzero 2 k ltac:(lia)) as Hpow.
  pose proof (Nat.pow_nonzero 2 (S k) ltac:(lia)) as Hpow'.
  assert (Hlog : Nat.log2 (Nat.pow 2 (S k) + m + Nat.pow 2 k) = S k).
  { apply Nat.log2_unique; simpl; lia. }
  assert (Hd : degree_is (S (S k))
    (assoc (S (S k)) (Nat.pow 2 (S k) + m) (Nat.pow 2 (S k) + m + Nat.pow 2 k))
    (assoc_degree (Nat.pow 2 (S k) + m) (Nat.pow 2 (S k) + m + Nat.pow 2 k))).
  { apply assoc_degree_is; simpl in *; lia. }
  unfold assoc_degree in Hd.
  rewrite (Nat.max_r (Nat.pow 2 (S k) + m) (Nat.pow 2 (S k) + m + Nat.pow 2 k)) in Hd by lia.
  rewrite Hlog in Hd. replace (S k - 1) with k in Hd by lia.
  rewrite Nat.max_r in Hd by lia. exact Hd.
Qed.
