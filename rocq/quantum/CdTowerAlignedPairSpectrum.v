(** The spectrum of the aligned-pair count and the mirror of its
    multiplicities: the Rocq bridge of five headline theorems of the Lean
    module lean/GororobaMath/CayleyDickson/AlignedPairSpectrum.lean.

    Convention: the one of CdTowerTwoTermRecursion.v. An index of level k
    is a nat below 2^k, the value of Lean's bit vector p : BitVec k
    (BitVec.toNat); Nat.lxor is the index of p ^^^ q; at level k + 1 the
    top bit of i is Nat.leb (2^k) i (Lean's BitVec.msb) and its low part
    i mod 2^k (Lean's setWidth k), and 2^k is the index of
    BitVec.cons true 0#k, the unit that the last doubling adjoins.
    TwoTermRecursion.aligned_pair_count k i j is Lean's
    Tower.alignedPairCount k i j (ci/compare_aligned_pair_count.sh
    compares the two on every pair up to level 7). Nat subtraction
    truncates in both provers, so 2^(k - 1) is 1 at k = 0 in both.

    multiplicity k n is Lean's Tower.alignedPairCountMultiplicity k n,
    the number of ordered pairs of indices below 2^k whose count is n,
    written as a double sum over the indices; ci/compare_aligned_pair_forms.sh
    evaluates both definitions on every level up to 5 and every n up to 16,
    and rejects a mutated Rocq reference.

    The module AlignedPairSpectrum restates, with N = aligned_pair_count:

    - aligned_pair_count_add_four_le_of_three_le is
      Tower.alignedPairCount_add_four_le_of_three_le: for k >= 3 every
      pair satisfies N k i j + 4 <= 2^(k - 1).
    - exists_aligned_pair_count_eq is Tower.exists_alignedPairCount_eq:
      every multiple 4 v with 4 v + 4 <= 2^(k - 1) is the count of a pair
      of nonzero distinct indices below 2^k.
    - range_aligned_pair_count is Tower.range_alignedPairCount: for k >= 3
      a nat n is the count of some pair of indices below 2^k exactly when
      4 divides n and n + 4 <= 2^(k - 1); Lean states the same as an
      equality of Set.range with a set.
    - aligned_pair_count_add_flip is Tower.alignedPairCount_add_flip:
      for indices below 2^(k + 1) with nonzero count,
      N (k + 1) i j + N (k + 1) i (j XOR 2^k) + 4 = 2^k.
    - multiplicity_mirror is Tower.multiplicity_mirror: for n <> 0 and
      n + 4 < 2^(k - 1), multiplicity k n =
      multiplicity k (2^(k - 1) - 4 - n).

    The proofs follow the Lean module and read the counts through the
    three recursions of CdTowerTwoTermRecursion.v alone.
    aligned_pair_count_shape is the joint content of Lean's
    Tower.four_dvd_alignedPairCount and
    Tower.alignedPairCount_eq_zero_or_add_four_le, proved by induction on
    k through the recursions: the same-half case doubles a count, the
    degenerate mixed case gives 0, and the nondegenerate mixed case gives
    2^k - 4 - 2 N k a b, which needs k >= 2 since a and b are nonzero and
    distinct below 2^k. The mirror pairs each j with j XOR 2^k
    (nsum_lxor, the invariance of a sum over the indices below 2^(k + 1)
    under this involution).

    The Rocq statements are narrower than the Lean ones in one respect: an
    index is a nat below 2^k, where Lean takes a BitVec k. The Lean
    theorems name no ring, and neither do these.
    aligned_pair_count_spectrum_level5 evaluates the set of counts at
    level 5, {0, 4, 8, 12}, and multiplicity_mirror_level5 one instance of
    the mirror. *)

From Stdlib Require Import Bool Lia PeanoNat List.
Require Import CdTowerTwoTermBridge CdTowerTwoTermRecursion.

Module AlignedPairSpectrum.
Import TwoTermRecursion.

Lemma pow2_pred k : (1 <= k)%nat -> Nat.pow 2 k = (2 * Nat.pow 2 (k - 1))%nat.
Proof. intro H. replace k with (S (k - 1)) at 1 by lia. apply Nat.pow_succ_r'. Qed.

Lemma pow2_split k : (2 <= k)%nat -> Nat.pow 2 k = (4 * Nat.pow 2 (k - 2))%nat.
Proof. intro H. replace k with (S (S (k - 2))) at 1 by lia. rewrite !Nat.pow_succ_r'. lia. Qed.

Lemma low_lt k i : (Nat.pow 2 k > 0)%nat -> (i mod Nat.pow 2 k < Nat.pow 2 k)%nat.
Proof. intro H. apply Nat.mod_upper_bound. lia. Qed.

(** Tower.alignedPairCount_zero_left. *)
Lemma aligned_pair_count_zero_left k : forall b, (b < Nat.pow 2 k)%nat -> aligned_pair_count k 0 b = O.
Proof.
  induction k as [|k IH]; intros b Hb.
  - cbn in Hb. assert (b = O) as -> by lia. apply aligned_pair_count_self.
  - pose proof (pow2_pos k) as Hn. pose proof (pow2_pos (S k)) as Hn1.
    assert (Z0 : Nat.leb (Nat.pow 2 k) 0 = false) by (apply Nat.leb_gt; lia).
    destruct (Nat.leb (Nat.pow 2 k) b) eqn:Eb.
    + apply aligned_pair_count_succ_eq_zero; [lia | exact Hb | rewrite Z0, Eb; discriminate |].
      left. apply Nat.Div0.mod_0_l.
    + rewrite aligned_pair_count_succ_of_msb_eq by (lia || congruence).
      rewrite Nat.Div0.mod_0_l, IH; [reflexivity |]. apply low_lt. lia.
Qed.

(** Tower.alignedPairCount_zero_right. *)
Lemma aligned_pair_count_zero_right k a : (a < Nat.pow 2 k)%nat -> aligned_pair_count k a 0 = O.
Proof. intro Ha. rewrite aligned_pair_count_comm. apply aligned_pair_count_zero_left. exact Ha. Qed.

(** Tower.alignedPairCount_low_ne_of_ne_zero: a nonzero count forces
    nonzero, distinct indices. *)
Lemma aligned_pair_count_low_ne k a b : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  aligned_pair_count k a b <> O -> a <> O /\ b <> O /\ a <> b.
Proof.
  intros Ha Hb H. split; [| split]; intro E; apply H; subst.
  - apply aligned_pair_count_zero_left. exact Hb.
  - apply aligned_pair_count_zero_right. exact Ha.
  - apply aligned_pair_count_self.
Qed.

(** Two nonzero distinct indices below 2^k exist only from k = 2 on. *)
Lemma two_le_of_distinct k a b : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  a <> O -> b <> O -> a <> b -> (2 <= k)%nat.
Proof. intros Ha Hb Ha0 Hb0 Hab. destruct k as [|[|k']]; cbn in Ha, Hb; lia. Qed.

(** Tower.four_dvd_alignedPairCount and
    Tower.alignedPairCount_eq_zero_or_add_four_le: every count is a
    multiple of 4, and a nonzero count satisfies N + 4 <= 2^(k - 1). *)
Lemma aligned_pair_count_shape k : forall i j, (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat ->
  (exists m, aligned_pair_count k i j = (4 * m)%nat) /\
  (aligned_pair_count k i j = O \/ (aligned_pair_count k i j + 4 <= Nat.pow 2 (k - 1))%nat).
Proof.
  induction k as [|k IH]; intros i j Hi Hj.
  - cbn in Hi, Hj. assert (i = O) as -> by lia. assert (j = O) as -> by lia.
    rewrite aligned_pair_count_self. split; [exists O; reflexivity | left; reflexivity].
  - pose proof (pow2_pos k) as Hn.
    pose proof (low_lt k i Hn) as Ha. pose proof (low_lt k j Hn) as Hb.
    destruct (IH _ _ Ha Hb) as [[m Hm] Hz].
    replace (S k - 1)%nat with k by lia.
    destruct (Bool.bool_dec (Nat.leb (Nat.pow 2 k) i) (Nat.leb (Nat.pow 2 k) j)) as [E | E].
    + rewrite (aligned_pair_count_succ_of_msb_eq k i j Hi Hj E).
      split; [exists (2 * m)%nat; lia |].
      destruct Hz as [Z | L]; [left; lia | right].
      destruct (Nat.eq_dec k 0) as [-> | Hk]; [cbn in L; lia |].
      pose proof (pow2_pred k ltac:(lia)). lia.
    + assert (D : (i mod Nat.pow 2 k = O \/ j mod Nat.pow 2 k = O \/ i mod Nat.pow 2 k = j mod Nat.pow 2 k) \/
        (i mod Nat.pow 2 k <> O /\ j mod Nat.pow 2 k <> O /\ i mod Nat.pow 2 k <> j mod Nat.pow 2 k)) by lia.
      destruct D as [D | [Ha0 [Hb0 Hab]]].
      * rewrite (aligned_pair_count_succ_eq_zero k i j Hi Hj E D).
        split; [exists O; reflexivity | left; reflexivity].
      * pose proof (aligned_pair_count_succ_add k i j Hi Hj E Ha0 Hb0 Hab) as S.
        pose proof (two_le_of_distinct k _ _ Ha Hb Ha0 Hb0 Hab) as Hk.
        pose proof (pow2_split k Hk).
        split; [exists (Nat.pow 2 (k - 2) - 1 - 2 * m)%nat; lia | right; lia].
Qed.

Lemma four_le_pow2_pred k : (3 <= k)%nat -> (4 <= Nat.pow 2 (k - 1))%nat.
Proof.
  intro Hk. rewrite (pow2_split (k - 1)) by lia. pose proof (pow2_pos (k - 1 - 2)). lia.
Qed.

(** Tower.alignedPairCount_add_four_le_of_three_le: from k = 3 on every
    pair satisfies N k i j + 4 <= 2^(k - 1), the count 0 included. *)
Theorem aligned_pair_count_add_four_le_of_three_le k i j :
  (3 <= k)%nat -> (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat ->
  (aligned_pair_count k i j + 4 <= Nat.pow 2 (k - 1))%nat.
Proof.
  intros Hk Hi Hj. pose proof (four_le_pow2_pred k Hk).
  destruct (aligned_pair_count_shape k i j Hi Hj) as [_ [Z | L]]; lia.
Qed.

(** Tower.exists_alignedPairCount_eq: every multiple 4 v with
    4 v + 4 <= 2^(k - 1) is the count of a pair of nonzero distinct
    indices below 2^k, at every level k. *)
Theorem exists_aligned_pair_count_eq : forall k v, (4 * v + 4 <= Nat.pow 2 (k - 1))%nat ->
  exists i j, (i < Nat.pow 2 k)%nat /\ (j < Nat.pow 2 k)%nat /\ i <> O /\ j <> O /\ i <> j /\
    aligned_pair_count k i j = (4 * v)%nat.
Proof.
  induction k as [|k IH]; intros v H.
  - cbn in H. lia.
  - replace (S k - 1)%nat with k in H by lia. pose proof (pow2_pos k) as Hn.
    destruct (Nat.lt_ge_cases k 3) as [Hk | Hk].
    + assert (E : k = 2%nat /\ v = O) by (destruct k as [|[|[|k']]]; cbn in H; lia).
      destruct E as [-> ->]. exists 1%nat, 2%nat.
      repeat split; first [vm_compute; reflexivity | cbn; lia].
    + assert (P1 : Nat.pow 2 (k - 1) = (4 * Nat.pow 2 (k - 3))%nat)
        by (rewrite (pow2_split (k - 1)) by lia; f_equal; f_equal; lia).
      assert (P0 : Nat.pow 2 k = (8 * Nat.pow 2 (k - 3))%nat) by (rewrite (pow2_pred k) by lia; lia).
      destruct (Nat.Even_or_Odd v) as [[w Ew] | [w Ew]].
      * destruct (IH w ltac:(lia)) as (a & b & Ha & Hb & Ha0 & Hb0 & Hab & HN).
        exists (cons k false a), (cons k false b).
        pose proof (aligned_pair_count_succ_of_msb_eq k (cons k false a) (cons k false b)
          (cons_lt k false a Ha) (cons_lt k false b Hb)) as S.
        rewrite !cons_top, !cons_mod in S by assumption.
        rewrite (S eq_refl), HN.
        split; [apply cons_lt; exact Ha |]. split; [apply cons_lt; exact Hb |].
        cbn [cons]. lia.
      * destruct (IH (Nat.pow 2 (k - 3) - 1 - w)%nat ltac:(lia)) as (a & b & Ha & Hb & Ha0 & Hb0 & Hab & HN).
        exists (cons k false a), (cons k true b).
        pose proof (aligned_pair_count_succ_add k (cons k false a) (cons k true b)
          (cons_lt k false a Ha) (cons_lt k true b Hb)) as S.
        rewrite !cons_top, !cons_mod in S by assumption.
        specialize (S ltac:(discriminate) Ha0 Hb0 Hab). rewrite HN in S.
        split; [apply cons_lt; exact Ha |]. split; [apply cons_lt; exact Hb |].
        cbn [cons] in S |- *. lia.
Qed.

(** Tower.range_alignedPairCount: for k >= 3 the counts of the pairs of
    indices below 2^k are exactly the multiples of 4 from 0 to
    2^(k - 1) - 4. *)
Theorem range_aligned_pair_count k : (3 <= k)%nat -> forall n,
  (exists i j, (i < Nat.pow 2 k)%nat /\ (j < Nat.pow 2 k)%nat /\ aligned_pair_count k i j = n) <->
  (Nat.divide 4 n /\ (n + 4 <= Nat.pow 2 (k - 1))%nat).
Proof.
  intros Hk n. split.
  - intros (i & j & Hi & Hj & <-). split.
    + destruct (aligned_pair_count_shape k i j Hi Hj) as [[m Hm] _]. exists m. lia.
    + apply aligned_pair_count_add_four_le_of_three_le; assumption.
  - intros [[v ->] H]. destruct (exists_aligned_pair_count_eq k v ltac:(lia)) as (i & j & Hi & Hj & _ & _ & _ & HN).
    exists i, j. split; [exact Hi |]. split; [exact Hj | lia].
Qed.

(** The flip j -> j XOR 2^k of level k + 1 moves j to the other half and
    keeps its low part. *)
Lemma flip_view k j : (j < Nat.pow 2 (S k))%nat ->
  (Nat.lxor j (Nat.pow 2 k) < Nat.pow 2 (S k))%nat /\
  Nat.leb (Nat.pow 2 k) (Nat.lxor j (Nat.pow 2 k)) = negb (Nat.leb (Nat.pow 2 k) j) /\
  Nat.lxor j (Nat.pow 2 k) mod Nat.pow 2 k = j mod Nat.pow 2 k.
Proof.
  intro Hj. pose proof (pow2_pos k) as Hn. destruct (cons_view k j Hj) as [Hb Ej].
  revert Ej Hb. generalize (Nat.leb (Nat.pow 2 k) j) (j mod Nat.pow 2 k). intros J b -> Hb.
  assert (Ec : cons k true 0 = Nat.pow 2 k) by reflexivity.
  assert (E : Nat.lxor (cons k J b) (Nat.pow 2 k) = cons k (negb J) b).
  { rewrite <- Ec, lxor_cons by (assumption || lia). rewrite Nat.lxor_0_r. destruct J; reflexivity. }
  rewrite E, !cons_top, !cons_mod by assumption. split; [apply cons_lt; exact Hb | split; reflexivity].
Qed.

Lemma lxor_flip_flip j c : Nat.lxor (Nat.lxor j c) c = j.
Proof. rewrite Nat.lxor_assoc, Nat.lxor_nilpotent, Nat.lxor_0_r. reflexivity. Qed.

(** Tower.alignedPairCount_add_flip: moving the second term of the operand
    to the other half of level k + 1 mirrors a nonzero count about
    2^k - 4. *)
Theorem aligned_pair_count_add_flip k i j : (i < Nat.pow 2 (S k))%nat -> (j < Nat.pow 2 (S k))%nat ->
  aligned_pair_count (S k) i j <> O ->
  (aligned_pair_count (S k) i j + aligned_pair_count (S k) i (Nat.lxor j (Nat.pow 2 k)) + 4)%nat =
    Nat.pow 2 k.
Proof.
  intros Hi Hj H. destruct (flip_view k j Hj) as [Hj' [Ej' Mj']].
  pose proof (pow2_pos k) as Hn.
  pose proof (low_lt k i Hn) as Ha. pose proof (low_lt k j Hn) as Hb.
  destruct (Bool.bool_dec (Nat.leb (Nat.pow 2 k) i) (Nat.leb (Nat.pow 2 k) j)) as [E | E].
  - pose proof (aligned_pair_count_succ_of_msb_eq k i j Hi Hj E) as Hs.
    assert (H' : aligned_pair_count k (i mod Nat.pow 2 k) (j mod Nat.pow 2 k) <> O) by lia.
    destruct (aligned_pair_count_low_ne k _ _ Ha Hb H') as [Ha0 [Hb0 Hab]].
    assert (E' : Nat.leb (Nat.pow 2 k) i <> Nat.leb (Nat.pow 2 k) (Nat.lxor j (Nat.pow 2 k)))
      by (rewrite Ej', E; destruct (Nat.leb (Nat.pow 2 k) j); discriminate).
    pose proof (aligned_pair_count_succ_add k i _ Hi Hj' E') as Hm.
    rewrite Mj' in Hm. specialize (Hm Ha0 Hb0 Hab). lia.
  - assert (D : (i mod Nat.pow 2 k = O \/ j mod Nat.pow 2 k = O \/ i mod Nat.pow 2 k = j mod Nat.pow 2 k) \/
      (i mod Nat.pow 2 k <> O /\ j mod Nat.pow 2 k <> O /\ i mod Nat.pow 2 k <> j mod Nat.pow 2 k)) by lia.
    destruct D as [D | [Ha0 [Hb0 Hab]]].
    + exfalso. apply H. exact (aligned_pair_count_succ_eq_zero k i j Hi Hj E D).
    + pose proof (aligned_pair_count_succ_add k i j Hi Hj E Ha0 Hb0 Hab) as Hm.
      assert (E' : Nat.leb (Nat.pow 2 k) i = Nat.leb (Nat.pow 2 k) (Nat.lxor j (Nat.pow 2 k)))
        by (rewrite Ej'; destruct (Nat.leb (Nat.pow 2 k) i), (Nat.leb (Nat.pow 2 k) j); cbn; congruence).
      pose proof (aligned_pair_count_succ_of_msb_eq k i _ Hi Hj' E') as Hs.
      rewrite Mj' in Hs. lia.
Qed.

(** Tower.alignedPairCountMultiplicity: the number of ordered pairs of
    indices below 2^k whose count is n. *)
Definition multiplicity (k n : nat) : nat :=
  nsum (Nat.pow 2 k) (fun i => nsum (Nat.pow 2 k) (fun j => ind (Nat.eqb (aligned_pair_count k i j) n))).

(** Tower.multiplicity_mirror: for n <> 0 and n + 4 < 2^(k - 1), as many
    ordered pairs have count n as have count 2^(k - 1) - 4 - n. *)
Theorem multiplicity_mirror k n : n <> O -> (n + 4 < Nat.pow 2 (k - 1))%nat ->
  multiplicity k n = multiplicity k (Nat.pow 2 (k - 1) - 4 - n).
Proof.
  intros Hn0 Hn. destruct k as [|k]; [cbn in Hn; lia |].
  replace (S k - 1)%nat with k in * by lia. unfold multiplicity.
  apply nsum_ext. intros i Hi.
  assert (Hc : (Nat.pow 2 k < Nat.pow 2 (S k))%nat) by (rewrite pow2_succ; pose proof (pow2_pos k); lia).
  transitivity (nsum (Nat.pow 2 (S k))
    (fun j => ind (Nat.eqb (aligned_pair_count (S k) i (Nat.lxor j (Nat.pow 2 k))) (Nat.pow 2 k - 4 - n)))).
  2: exact (nsum_lxor (S k) (Nat.pow 2 k)
       (fun j => ind (Nat.eqb (aligned_pair_count (S k) i j) (Nat.pow 2 k - 4 - n))) Hc).
  apply nsum_ext. intros j Hj. f_equal. destruct (flip_view k j Hj) as [Hj' _].
  destruct (Nat.eqb_spec (aligned_pair_count (S k) i j) n) as [E1 | E1],
    (Nat.eqb_spec (aligned_pair_count (S k) i (Nat.lxor j (Nat.pow 2 k))) (Nat.pow 2 k - 4 - n)) as [E2 | E2];
    try reflexivity; exfalso.
  - apply E2. pose proof (aligned_pair_count_add_flip k i j Hi Hj ltac:(lia)). lia.
  - apply E1. pose proof (aligned_pair_count_add_flip k i _ Hi Hj' ltac:(lia)) as F.
    rewrite lxor_flip_flip in F. lia.
Qed.

End AlignedPairSpectrum.

(** The counts at level 5 are {0, 4, 8, 12}, the multiples of 4 up to
    2^4 - 4 (Tower.range_alignedPairCount at k = 5; the pairs (1, 17),
    (1, 26), (1, 10) and (1, 18) carry them, Tower.alignedPairCount_pathion_1_17,
    _1_26 and _1_18 of TwoTerm.lean among them), and no pair carries 16. *)
Example aligned_pair_count_spectrum_level5 :
  TwoTermRecursion.aligned_pair_count 5 1 17 = 0%nat /\
  TwoTermRecursion.aligned_pair_count 5 1 26 = 4%nat /\
  TwoTermRecursion.aligned_pair_count 5 1 10 = 8%nat /\
  TwoTermRecursion.aligned_pair_count 5 1 18 = 12%nat /\
  AlignedPairSpectrum.multiplicity 5 16 = 0%nat.
Proof. vm_compute. repeat split. Qed.

(** Tower.multiplicity_mirror at k = 5 and n = 4: as many ordered pairs
    have count 4 as have count 2^4 - 4 - 4 = 8. *)
Example multiplicity_mirror_level5 :
  AlignedPairSpectrum.multiplicity 5 4 = AlignedPairSpectrum.multiplicity 5 8.
Proof. vm_compute. reflexivity. Qed.
