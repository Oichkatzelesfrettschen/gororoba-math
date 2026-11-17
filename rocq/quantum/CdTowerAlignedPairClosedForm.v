(** A closed form of the aligned-pair count: the Rocq bridge of the headline
    theorem of the Lean module
    lean/GororobaMath/CayleyDickson/AlignedPairClosedForm.lean.

    Convention: the one of CdTowerTwoTermRecursion.v. An index of level k
    is a nat below 2^k, the value of Lean's bit vector p : BitVec k
    (BitVec.toNat), and bit s of an index is Nat.testbit i s (Lean's
    BitVec.getLsbD p s; both are false from s = k on). Nat subtraction
    truncates in both provers. TwoTermRecursion.aligned_pair_count k i j is
    Lean's Tower.alignedPairCount k i j (ci/compare_aligned_pair_count.sh).

    The definitions transcribe the Lean ones, with each decidable
    proposition a bool and each finite sum an nsum:

    - degenerate_split i j p is Tower.DegenerateSplit i j p: bit p of i
      and of j differ, and below bit p the index i is zero, j is zero, or
      the two agree, each quantifier over s < p a forallb over seq 0 p.
    - cleared_xor_bit k i j s is Tower.clearedXorBit i j s: bit s of
      i XOR j, kept when every degenerate split p < k lies below s.
    - isum t n g is the sum of g s over t <= s < n, Lean's
      sum over Finset.Ico t n.
    - cleared_xor_parity k i j t is Tower.clearedXorParity i j t, the
      parity of the kept bits at positions t to k - 1.
    - closed_form k i j is Tower.closedForm k i j,
      4 * sum over 3 <= t < k of 2^(k - 1 - t) * parity t.

    ci/compare_aligned_pair_forms.sh evaluates closed_form, the cleared
    bits as one index and the degenerate splits as one index on every pair
    up to level 6, against the Lean definitions, and rejects a mutated
    Rocq closed form that keeps every bit of i XOR j.

    The module AlignedPairClosedForm restates
    aligned_pair_count_eq_closed_form, Tower.alignedPairCount_eq_closedForm:
    for i and j below 2^k, aligned_pair_count k i j = closed_form k i j.
    The proof follows the Lean one, an induction on k through the three
    cases of the doubling recursion of CdTowerTwoTermRecursion.v: below
    level 4 both sides are 0 (aligned_pair_count_shape of
    CdTowerAlignedPairSpectrum.v bounds the count by 2^(k - 1) - 4); the
    same-half case doubles both sides; the degenerate mixed case clears
    every bit of the kept exclusive or; and the nondegenerate mixed case
    complements every parity below the top bit, which gives
    F (k + 1) + 2 F k + 4 = 2^k through
    sum over 3 <= t < k of 2^(k - t) = 2^(k - 2) - 2.

    The Rocq statement is narrower than the Lean one in one respect: an
    index is a nat below 2^k, where Lean takes a BitVec k.
    closed_form_level5 evaluates the closed form on the pairs that
    TwoTerm.lean decides at level 5, among them the degenerate pair
    (1, 17), whose low parts agree. *)

From Stdlib Require Import Bool Lia PeanoNat List.
Require CdTowerBasisSign.
Require Import CdTowerTwoTermBridge CdTowerTwoTermRecursion CdTowerAlignedPairSpectrum.

Module AlignedPairClosedForm.
Import TwoTermRecursion.

(** Tower.DegenerateSplit: bit p of i and of j differ, and below bit p
    the index i is zero, j is zero, or the two agree. *)
Definition degenerate_split (i j p : nat) : bool :=
  negb (Bool.eqb (Nat.testbit i p) (Nat.testbit j p)) &&
  (forallb (fun s => negb (Nat.testbit i s)) (seq 0 p) ||
   forallb (fun s => negb (Nat.testbit j s)) (seq 0 p) ||
   forallb (fun s => Bool.eqb (Nat.testbit i s) (Nat.testbit j s)) (seq 0 p)).

(** Tower.clearedXorBit: bit s of i XOR j, kept when every degenerate
    split below k lies below position s. *)
Definition cleared_xor_bit (k i j s : nat) : bool :=
  xorb (Nat.testbit i s) (Nat.testbit j s) &&
  forallb (fun p => negb (degenerate_split i j p) || Nat.ltb p s) (seq 0 k).

(** The sum of g s over t <= s < n, Lean's sum over Finset.Ico t n. *)
Definition isum (t n : nat) (g : nat -> nat) : nat := nsum (n - t) (fun d => g (t + d)%nat).

(** Tower.clearedXorParity: the parity of the kept bits at positions t to
    k - 1. *)
Definition cleared_xor_parity (k i j t : nat) : nat :=
  isum t k (fun s => ind (cleared_xor_bit k i j s)) mod 2.

(** Tower.closedForm: 4 * sum over 3 <= t < k of 2^(k - 1 - t) * parity t. *)
Definition closed_form (k i j : nat) : nat :=
  4 * isum 3 k (fun t => Nat.pow 2 (k - 1 - t) * cleared_xor_parity k i j t).

Lemma forallb_ext_seq n f g : (forall s, (s < n)%nat -> f s = g s) -> forallb f (seq 0 n) = forallb g (seq 0 n).
Proof.
  intro E. apply Bool.eq_true_iff_eq. rewrite !forallb_forall.
  split; intros H s Hs; pose proof (proj1 (in_seq n 0 s) Hs) as L; specialize (H s Hs);
    [rewrite <- E | rewrite E]; (assumption || lia).
Qed.

Lemma forallb_seq_succ n f : forallb f (seq 0 (S n)) = forallb f (seq 0 n) && f n.
Proof. rewrite seq_S, forallb_app. cbn. rewrite andb_true_r. reflexivity. Qed.

Lemma testbit_high k a s : (a < Nat.pow 2 k)%nat -> (k <= s)%nat -> Nat.testbit a s = false.
Proof.
  intros Ha Hs. apply Nat.testbit_false. rewrite Nat.div_small; [reflexivity |].
  apply Nat.lt_le_trans with (Nat.pow 2 k); [exact Ha | apply Nat.pow_le_mono_r; lia].
Qed.

Lemma testbit_cons_lt k I a s : (a < Nat.pow 2 k)%nat -> (s < k)%nat ->
  Nat.testbit (cons k I a) s = Nat.testbit a s.
Proof. intros Ha Hs. rewrite <- (Nat.mod_pow2_bits_low (cons k I a) k s Hs), cons_mod by assumption. reflexivity. Qed.

Lemma testbit_cons_self k I a : (a < Nat.pow 2 k)%nat -> Nat.testbit (cons k I a) k = I.
Proof.
  intro Ha. pose proof (pow2_pos k) as Hn. destruct I; cbn [cons].
  - apply Nat.testbit_true. replace (a + Nat.pow 2 k)%nat with (a + 1 * Nat.pow 2 k)%nat by lia.
    rewrite Nat.div_add, Nat.div_small by lia. reflexivity.
  - apply (testbit_high k a k Ha). lia.
Qed.

(** Below bit k, an index below 2^k has no set bit exactly when it is 0. *)
Lemma forallb_zero k a : (a < Nat.pow 2 k)%nat -> forallb (fun s => negb (Nat.testbit a s)) (seq 0 k) = Nat.eqb a 0.
Proof.
  intro Ha. destruct (Nat.eqb_spec a 0) as [-> | H0].
  - apply forallb_forall. intros s _. rewrite Nat.bits_0. reflexivity.
  - apply Bool.not_true_is_false. intro F. rewrite forallb_forall in F.
    pose proof (proj1 (Nat.log2_lt_pow2 a k ltac:(lia)) Ha) as L.
    specialize (F (Nat.log2 a) ltac:(apply in_seq; lia)). rewrite Nat.bit_log2 in F by exact H0. discriminate F.
Qed.

Lemma forallb_eq k a b : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  forallb (fun s => Bool.eqb (Nat.testbit a s) (Nat.testbit b s)) (seq 0 k) = Nat.eqb a b.
Proof.
  intros Ha Hb. rewrite <- CdTowerBasisSign.lxor_eqb_0.
  rewrite <- (forallb_zero k (Nat.lxor a b)) by (apply CdTowerBasisSign.lxor_lt; assumption).
  apply forallb_ext_seq. intros s _. rewrite Nat.lxor_spec.
  destruct (Nat.testbit a s), (Nat.testbit b s); reflexivity.
Qed.

(** Tower.degenerateSplit_cons_of_lt. *)
Lemma degenerate_split_cons_lt k I J a b p : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat -> (p < k)%nat ->
  degenerate_split (cons k I a) (cons k J b) p = degenerate_split a b p.
Proof.
  intros Ha Hb Hp. unfold degenerate_split. rewrite !testbit_cons_lt by assumption.
  rewrite (forallb_ext_seq p (fun s => negb (Nat.testbit (cons k I a) s)) (fun s => negb (Nat.testbit a s)))
    by (intros s Hs; rewrite testbit_cons_lt by lia; reflexivity).
  rewrite (forallb_ext_seq p (fun s => negb (Nat.testbit (cons k J b) s)) (fun s => negb (Nat.testbit b s)))
    by (intros s Hs; rewrite testbit_cons_lt by lia; reflexivity).
  rewrite (forallb_ext_seq p (fun s => Bool.eqb (Nat.testbit (cons k I a) s) (Nat.testbit (cons k J b) s))
    (fun s => Bool.eqb (Nat.testbit a s) (Nat.testbit b s)))
    by (intros s Hs; rewrite !testbit_cons_lt by lia; reflexivity).
  reflexivity.
Qed.

(** Tower.degenerateSplit_cons_self: the split at the top bit of level
    k + 1 is degenerate when the top bits differ and the low parts satisfy
    a = 0, b = 0 or a = b. *)
Lemma degenerate_split_cons_self k I J a b : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  degenerate_split (cons k I a) (cons k J b) k =
  negb (Bool.eqb I J) && (Nat.eqb a 0 || Nat.eqb b 0 || Nat.eqb a b).
Proof.
  intros Ha Hb. unfold degenerate_split. rewrite !testbit_cons_self by assumption.
  rewrite (forallb_ext_seq k (fun s => negb (Nat.testbit (cons k I a) s)) (fun s => negb (Nat.testbit a s)))
    by (intros s Hs; rewrite testbit_cons_lt by lia; reflexivity).
  rewrite (forallb_ext_seq k (fun s => negb (Nat.testbit (cons k J b) s)) (fun s => negb (Nat.testbit b s)))
    by (intros s Hs; rewrite testbit_cons_lt by lia; reflexivity).
  rewrite (forallb_ext_seq k (fun s => Bool.eqb (Nat.testbit (cons k I a) s) (Nat.testbit (cons k J b) s))
    (fun s => Bool.eqb (Nat.testbit a s) (Nat.testbit b s)))
    by (intros s Hs; rewrite !testbit_cons_lt by lia; reflexivity).
  rewrite (forallb_zero k a Ha), (forallb_zero k b Hb), (forallb_eq k a b Ha Hb). reflexivity.
Qed.

(** Tower.clearedXorBit_cons_of_degenerate. *)
Lemma cleared_xor_bit_cons_degenerate k I J a b s :
  degenerate_split (cons k I a) (cons k J b) k = true -> (s <= k)%nat ->
  cleared_xor_bit (S k) (cons k I a) (cons k J b) s = false.
Proof.
  intros Hd Hs. unfold cleared_xor_bit. rewrite forallb_seq_succ, Hd, (proj2 (Nat.ltb_ge k s) Hs).
  cbn [negb orb]. rewrite !andb_false_r. reflexivity.
Qed.

(** Tower.clearedXorBit_cons_of_lt. *)
Lemma cleared_xor_bit_cons_lt k I J a b s : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  degenerate_split (cons k I a) (cons k J b) k = false -> (s < k)%nat ->
  cleared_xor_bit (S k) (cons k I a) (cons k J b) s = cleared_xor_bit k a b s.
Proof.
  intros Ha Hb Hd Hs. unfold cleared_xor_bit. rewrite forallb_seq_succ, Hd. cbn [negb orb].
  rewrite andb_true_r, !testbit_cons_lt by assumption. f_equal.
  apply forallb_ext_seq. intros p Hp. rewrite degenerate_split_cons_lt by assumption. reflexivity.
Qed.

(** Tower.clearedXorBit_cons_self. *)
Lemma cleared_xor_bit_cons_self k I J a b : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  degenerate_split (cons k I a) (cons k J b) k = false ->
  cleared_xor_bit (S k) (cons k I a) (cons k J b) k = xorb I J.
Proof.
  intros Ha Hb Hd. unfold cleared_xor_bit. rewrite forallb_seq_succ, Hd. cbn [negb orb].
  rewrite andb_true_r, !testbit_cons_self by assumption.
  assert (F : forallb (fun p => negb (degenerate_split (cons k I a) (cons k J b) p) || Nat.ltb p k) (seq 0 k) = true).
  { apply forallb_forall. intros p Hp. apply in_seq in Hp. rewrite (proj2 (Nat.ltb_lt p k)) by lia. apply orb_true_r. }
  rewrite F. apply andb_true_r.
Qed.

Lemma isum_succ_top t n g : (t <= n)%nat -> isum t (S n) g = (isum t n g + g n)%nat.
Proof.
  intro H. unfold isum. replace (S n - t)%nat with (S (n - t)) by lia. cbn [nsum].
  replace (t + (n - t))%nat with n by lia. reflexivity.
Qed.

Lemma isum_ext t n g h : (forall s, (t <= s)%nat -> (s < n)%nat -> g s = h s) -> isum t n g = isum t n h.
Proof. intro E. unfold isum. apply nsum_ext. intros d Hd. apply E; lia. Qed.

Lemma isum_empty t n g : (n <= t)%nat -> isum t n g = O.
Proof. intro H. unfold isum. replace (n - t)%nat with O by lia. reflexivity. Qed.

Lemma isum_zero t n : isum t n (fun _ => O) = O.
Proof. unfold isum. apply nsum_zero. intros. reflexivity. Qed.

Lemma isum_scale c t n g : (c * isum t n g)%nat = isum t n (fun s => c * g s)%nat.
Proof.
  unfold isum. induction (n - t)%nat as [|m IH]; cbn [nsum]; [lia |].
  rewrite Nat.mul_add_distr_l, IH. reflexivity.
Qed.

Lemma isum_add t n g h : isum t n (fun s => g s + h s)%nat = (isum t n g + isum t n h)%nat.
Proof. unfold isum. apply nsum_add. Qed.

Lemma parity_complement n : ((n + 1) mod 2 + n mod 2)%nat = 1%nat.
Proof.
  pose proof (Nat.div_mod_eq n 2). pose proof (Nat.div_mod_eq (n + 1) 2).
  pose proof (Nat.mod_upper_bound n 2 ltac:(lia)). pose proof (Nat.mod_upper_bound (n + 1) 2 ltac:(lia)). lia.
Qed.

(** The kept bits of level k + 1 from position t, below a nondegenerate
    top split: those of level k and the top bit I XOR J. *)
Lemma sum_cleared_xor_bit_cons k I J a b t : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  degenerate_split (cons k I a) (cons k J b) k = false -> (t <= k)%nat ->
  isum t (S k) (fun s => ind (cleared_xor_bit (S k) (cons k I a) (cons k J b) s)) =
    (isum t k (fun s => ind (cleared_xor_bit k a b s)) + ind (xorb I J))%nat.
Proof.
  intros Ha Hb Hd Ht. rewrite isum_succ_top by assumption. cbv beta.
  rewrite cleared_xor_bit_cons_self by assumption. f_equal.
  apply isum_ext. intros s _ Hs. rewrite cleared_xor_bit_cons_lt by assumption. reflexivity.
Qed.

Lemma closed_form_le_three k i j : (k <= 3)%nat -> closed_form k i j = O.
Proof. intro H. unfold closed_form. rewrite isum_empty by lia. reflexivity. Qed.

Lemma parity_top k i j : cleared_xor_parity k i j k = O.
Proof. unfold cleared_xor_parity. rewrite isum_empty by lia. reflexivity. Qed.

(** Tower.closedForm_cons_of_degenerate. *)
Lemma closed_form_cons_degenerate k I J a b :
  degenerate_split (cons k I a) (cons k J b) k = true -> closed_form (S k) (cons k I a) (cons k J b) = O.
Proof.
  intro Hd. unfold closed_form. rewrite (isum_ext 3 (S k) _ (fun _ => O)); [rewrite isum_zero; reflexivity |].
  intros t _ Ht. unfold cleared_xor_parity.
  rewrite (isum_ext t (S k) _ (fun _ => O)); [rewrite isum_zero; cbn; lia |].
  intros s _ Hs. rewrite cleared_xor_bit_cons_degenerate by (assumption || lia). reflexivity.
Qed.

(** Tower.closedForm_cons_same: the same-half step doubles the closed
    form. *)
Lemma closed_form_cons_same k I a b : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  closed_form (S k) (cons k I a) (cons k I b) = (2 * closed_form k a b)%nat.
Proof.
  intros Ha Hb.
  assert (Hd : degenerate_split (cons k I a) (cons k I b) k = false)
    by (rewrite degenerate_split_cons_self by assumption; destruct I; reflexivity).
  assert (Hp : forall t, (t <= k)%nat ->
    cleared_xor_parity (S k) (cons k I a) (cons k I b) t = cleared_xor_parity k a b t).
  { intros t Ht. unfold cleared_xor_parity. rewrite sum_cleared_xor_bit_cons by assumption.
    destruct I; cbn [xorb ind]; rewrite Nat.add_0_r; reflexivity. }
  destruct (Nat.lt_ge_cases k 3) as [Hk | Hk].
  { rewrite !closed_form_le_three by lia. reflexivity. }
  unfold closed_form. rewrite isum_succ_top by lia. cbv beta.
  rewrite (Hp k (le_n k)), parity_top, Nat.mul_0_r, Nat.add_0_r.
  rewrite (isum_ext 3 k _ (fun t => 2 * (Nat.pow 2 (k - 1 - t) * cleared_xor_parity k a b t))%nat).
  - rewrite <- isum_scale. lia.
  - intros t _ Ht. rewrite (Hp t) by lia. replace (S k - 1 - t)%nat with (S (k - 1 - t)) by lia.
    rewrite Nat.pow_succ_r'. lia.
Qed.

(** sum over 3 <= t < k of 2^(k - t), plus 2, is 2^(k - 2). *)
Lemma sum_two_pow k : (3 <= k)%nat -> (isum 3 k (fun t => Nat.pow 2 (k - t)) + 2)%nat = Nat.pow 2 (k - 2).
Proof.
  induction k as [|k IH]; intro Hk; [lia |].
  destruct (Nat.eq_dec k 2) as [-> | Hk2]; [reflexivity |].
  rewrite isum_succ_top by lia. cbv beta.
  rewrite (isum_ext 3 k _ (fun t => 2 * Nat.pow 2 (k - t))%nat).
  - rewrite <- isum_scale. replace (S k - k)%nat with 1%nat by lia.
    replace (S k - 2)%nat with (S (k - 2)) by lia. rewrite Nat.pow_1_r, Nat.pow_succ_r'.
    specialize (IH ltac:(lia)). lia.
  - intros t _ Ht. replace (S k - t)%nat with (S (k - t)) by lia. apply Nat.pow_succ_r'.
Qed.

(** Tower.closedForm_cons_mixed_add: the nondegenerate mixed step,
    F (k + 1) + 2 F k + 4 = 2^k. *)
Lemma closed_form_cons_mixed_add k I J a b : (3 <= k)%nat -> I <> J ->
  (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  degenerate_split (cons k I a) (cons k J b) k = false ->
  (closed_form (S k) (cons k I a) (cons k J b) + 2 * closed_form k a b + 4)%nat = Nat.pow 2 k.
Proof.
  intros Hk HIJ Ha Hb Hd.
  assert (Hx : ind (xorb I J) = 1%nat) by (destruct I, J; cbn; congruence).
  assert (Hp : forall t, (t <= k)%nat ->
    (cleared_xor_parity (S k) (cons k I a) (cons k J b) t + cleared_xor_parity k a b t)%nat = 1%nat).
  { intros t Ht. unfold cleared_xor_parity. rewrite sum_cleared_xor_bit_cons, Hx by assumption.
    apply parity_complement. }
  assert (Hk1 : cleared_xor_parity (S k) (cons k I a) (cons k J b) k = 1%nat)
    by (pose proof (Hp k (le_n k)); rewrite parity_top in *; lia).
  pose proof (sum_two_pow k Hk) as G. pose proof (AlignedPairSpectrum.pow2_split k ltac:(lia)) as P.
  unfold closed_form. rewrite isum_succ_top by lia. cbv beta.
  rewrite Hk1. replace (S k - 1 - k)%nat with O by lia. rewrite Nat.pow_0_r.
  assert (Hs : (isum 3 k (fun t => Nat.pow 2 (S k - 1 - t) * cleared_xor_parity (S k) (cons k I a) (cons k J b) t) +
      2 * isum 3 k (fun t => Nat.pow 2 (k - 1 - t) * cleared_xor_parity k a b t))%nat =
    isum 3 k (fun t => Nat.pow 2 (k - t))).
  { rewrite isum_scale, <- isum_add. apply isum_ext. intros t _ Ht.
    pose proof (Hp t ltac:(lia)) as H1.
    replace (S k - 1 - t)%nat with (k - t)%nat by lia.
    replace (k - t)%nat with (S (k - 1 - t)) by lia. rewrite Nat.pow_succ_r'.
    revert H1. generalize (cleared_xor_parity (S k) (cons k I a) (cons k J b) t) (cleared_xor_parity k a b t).
    intros p q H1. assert (p = (1 - q)%nat /\ (q <= 1)%nat) as [-> Hq] by lia.
    destruct q as [|[|q]]; [lia | lia | lia]. }
  lia.
Qed.

(** Every count at a level up to 3 is 0. *)
Lemma aligned_pair_count_eq_zero_of_le_three k i j : (k <= 3)%nat -> (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat ->
  aligned_pair_count k i j = O.
Proof.
  intros Hk Hi Hj. destruct (AlignedPairSpectrum.aligned_pair_count_shape k i j Hi Hj) as [_ [Z | L]]; [exact Z |].
  destruct k as [|[|[|[|k]]]]; cbn in L; lia.
Qed.

(** Tower.alignedPairCount_eq_closedForm: at every level and for all
    indices below 2^k, the aligned-pair count is the closed form. *)
Theorem aligned_pair_count_eq_closed_form : forall k i j, (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat ->
  aligned_pair_count k i j = closed_form k i j.
Proof.
  induction k as [|k IH]; intros i j Hi Hj.
  { rewrite closed_form_le_three by lia. apply aligned_pair_count_eq_zero_of_le_three; [lia | assumption | assumption]. }
  destruct (Nat.lt_ge_cases k 3) as [Hk | Hk].
  { rewrite closed_form_le_three by lia. apply aligned_pair_count_eq_zero_of_le_three; [lia | assumption | assumption]. }
  destruct (cons_view k i Hi) as [Ha Ei]. destruct (cons_view k j Hj) as [Hb Ej].
  revert Ei Ej Ha Hb.
  generalize (Nat.leb (Nat.pow 2 k) i) (Nat.leb (Nat.pow 2 k) j) (i mod Nat.pow 2 k) (j mod Nat.pow 2 k).
  intros I J a b Ei Ej Ha Hb. subst i j.
  pose proof (IH a b Ha Hb) as Iab.
  destruct (Bool.bool_dec I J) as [<- | HIJ].
  - pose proof (aligned_pair_count_succ_of_msb_eq k (cons k I a) (cons k I b) (cons_lt k I a Ha) (cons_lt k I b Hb)) as Hs.
    rewrite !cons_top, !cons_mod in Hs by assumption.
    rewrite (Hs eq_refl), closed_form_cons_same by assumption. lia.
  - assert (EIJ : negb (Bool.eqb I J) = true) by (destruct I, J; cbn; congruence).
    pose proof (degenerate_split_cons_self k I J a b Ha Hb) as Dself. rewrite EIJ in Dself. cbn [andb] in Dself.
    destruct (degenerate_split (cons k I a) (cons k J b) k) eqn:Dg.
    + rewrite closed_form_cons_degenerate by assumption.
      apply (aligned_pair_count_succ_eq_zero k); [apply cons_lt; assumption | apply cons_lt; assumption | |].
      * rewrite !cons_top by assumption. exact HIJ.
      * rewrite !cons_mod by assumption.
        destruct (Nat.eqb_spec a 0), (Nat.eqb_spec b 0), (Nat.eqb_spec a b); cbn [orb] in Dself;
          first [tauto | discriminate Dself].
    + assert (Hnd : a <> O /\ b <> O /\ a <> b)
        by (destruct (Nat.eqb_spec a 0), (Nat.eqb_spec b 0), (Nat.eqb_spec a b); cbn [orb] in Dself;
              first [discriminate Dself | tauto]).
      destruct Hnd as [Ha0 [Hb0 Hab]].
      pose proof (aligned_pair_count_succ_add k (cons k I a) (cons k J b) (cons_lt k I a Ha) (cons_lt k J b Hb)) as Hs.
      rewrite !cons_top, !cons_mod in Hs by assumption. specialize (Hs HIJ Ha0 Hb0 Hab).
      pose proof (closed_form_cons_mixed_add k I J a b Hk HIJ Ha Hb Dg) as Hf. lia.
Qed.

End AlignedPairClosedForm.

(** The closed form at the pairs that TwoTerm.lean decides at level 5
    (Tower.alignedPairCount_pathion_1_18, _1_24, _1_17, _1_26 and _2_27):
    (1, 17) lies in different halves with equal low parts 1, a degenerate
    top split. *)
Example closed_form_level5 :
  AlignedPairClosedForm.closed_form 5 1 18 = 12%nat /\
  AlignedPairClosedForm.closed_form 5 1 24 = 12%nat /\
  AlignedPairClosedForm.closed_form 5 1 17 = 0%nat /\
  AlignedPairClosedForm.closed_form 5 1 26 = 4%nat /\
  AlignedPairClosedForm.closed_form 5 2 27 = 4%nat /\
  AlignedPairClosedForm.degenerate_split 1 17 4 = true.
Proof. vm_compute. repeat split. Qed.
