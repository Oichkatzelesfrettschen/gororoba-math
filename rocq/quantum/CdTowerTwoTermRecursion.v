(** The doubling recursion of the aligned-pair count of a two-term
    operand: the Rocq bridge of three headline theorems of the Lean module
    lean/GororobaMath/CayleyDickson/TwoTermRecursion.lean.

    Convention: an index of level k is a nat below 2^k, the value of
    Lean's bit vector p : BitVec k (BitVec.toNat). Nat.lxor is the index of
    p ^^^ q, and TowerSign.neg_sign of CdTowerBasisBridge.v is Lean's
    Tower.negSign with the same argument order. A bit vector of width
    k + 1 has the top bit Nat.leb (2^k) i (Lean's BitVec.msb) and the low
    part i mod 2^k (Lean's setWidth k, BitVec.toNat_setWidth); cons k b y
    is the index whose top bit is b and whose low part is y (Lean's
    BitVec.cons b y).

    The alignment test is the one of CdTowerTwoTermBridge.v, partner,
    aligned_add and aligned_sub of the functor TwoTermBridge, which
    compose neg_sign with Nat.lxor alone and do not depend on the
    coefficient ring; this file reads them at the integer instance
    IntegerTwoTermBridge. aligned_pair_count k i j transcribes Lean's
    Tower.alignedPairCount k i j: 0 for i = j, and otherwise half the
    number of indices x below 2^k with aligned_add k i j x or
    aligned_sub k i j x, counted over seq 0 (2^k), the list
    List.range (2 ^ k) of Lean. No proof joins the two definitions, so
    ci/compare_aligned_pair_count.sh evaluates both on every pair i, j at
    the levels 0 to 7 and rejects a mutated Rocq count.

    The module TwoTermRecursion restates the three cases of the recursion,
    for i and j below 2^(k + 1) with low parts a = i mod 2^k and
    b = j mod 2^k and N = aligned_pair_count:

    - aligned_pair_count_succ_of_msb_eq is
      Tower.alignedPairCount_succ_of_msb_eq: i and j in the same half give
      N (k + 1) i j = 2 * N k a b.
    - aligned_pair_count_succ_eq_zero is
      Tower.alignedPairCount_succ_eq_zero: i and j in different halves
      with a = 0, b = 0 or a = b give N (k + 1) i j = 0.
    - aligned_pair_count_succ_add is Tower.alignedPairCount_succ_add: i
      and j in different halves with nonzero distinct low parts give
      N (k + 1) i j + 2 * N k a b + 4 = 2^k.

    The proof follows the Lean module. neg_sign_cons is Tower.negSign_cons
    on nat indices: the sign of level k + 1 is the sign of the low parts
    with a transposition correction (tr) when the right index lies in the
    second half and conjugation corrections when the left index does.
    misaligned k i j x is Tower.misaligned, true when the four signs of the
    pair {x, partner i j x} multiply to -1; aligned_misaligned ties it to
    the tranche-2 test. For i and j in the same half the corrections
    cancel (misaligned_cons_same); for i and j in different halves a low
    index outside {0, a, b, a XOR b} changes its alignment
    (misaligned_cons_mixed), the four exceptional indices are aligned at
    neither level (misaligned_special), and no index is aligned when
    a = 0, b = 0 or a = b (misaligned_cons_degenerate). Sums run through
    nsum; nsum_lxor is the invariance of a sum over the indices below 2^k
    under x -> x XOR c, which pairs each half with the other and gives
    aligned_count_reps: for i <> j the aligned indices are twice the
    representatives x < partner i j x of the aligned pairs, the count
    that CdTowerTwoTermNullity.v reads as the size of a kernel basis.

    The Rocq statements are narrower than the Lean ones in one respect:
    an index is a nat below 2^(k + 1), where Lean takes a BitVec (k + 1).
    The Lean theorems name no ring, and neither do these. Two instances
    evaluate the Lean module's counts at level 5. *)

From Stdlib Require Import Bool Btauto Lia PeanoNat List.
Require CdTowerBasisSign.
Require Import CdTowerBasisBridge CdTowerTwoTermBridge.

Module TwoTermRecursion.
Import TowerSign IntegerTwoTermBridge.

(** Tower.alignedPairCount on nat indices. *)
Definition aligned_pair_count (k i j : nat) : nat :=
  if Nat.eqb i j then O
  else length (filter (fun x => orb (aligned_add k i j x) (aligned_sub k i j x))
    (seq 0 (Nat.pow 2 k))) / 2.

(** Sums of nat-valued functions over the indices below n. *)
Fixpoint nsum (n : nat) (g : nat -> nat) : nat :=
  match n with O => O | S m => nsum m g + g m end.

Definition ind (b : bool) : nat := if b then 1 else 0.

Lemma nsum_ext n g h : (forall m, (m < n)%nat -> g m = h m) -> nsum n g = nsum n h.
Proof.
  induction n as [|m IH]; intro E; cbn [nsum]; [reflexivity |].
  rewrite IH by (intros; apply E; lia). rewrite E by lia. reflexivity.
Qed.

Lemma nsum_add n g h : nsum n (fun m => g m + h m) = nsum n g + nsum n h.
Proof. induction n as [|m IH]; cbn [nsum]; [reflexivity | rewrite IH; lia]. Qed.

Lemma nsum_const_one n : nsum n (fun _ => 1) = n.
Proof. induction n as [|m IH]; cbn [nsum]; [reflexivity | rewrite IH; lia]. Qed.

Lemma nsum_zero n g : (forall m, (m < n)%nat -> g m = O) -> nsum n g = O.
Proof.
  induction n as [|m IH]; intro E; cbn [nsum]; [reflexivity |].
  rewrite IH by (intros; apply E; lia). rewrite E by lia. reflexivity.
Qed.

Lemma nsum_shift m n g : nsum (m + n) g = nsum m g + nsum n (fun y => g (m + y)).
Proof.
  induction n as [|n IH].
  - rewrite Nat.add_0_r. cbn [nsum]. lia.
  - rewrite Nat.add_succ_r. cbn [nsum]. rewrite IH. lia.
Qed.

Lemma nsum_delta n c : (c < n)%nat -> nsum n (fun y => ind (Nat.eqb y c)) = 1.
Proof.
  induction n as [|m IH]; intro Hc; [lia |]. cbn [nsum].
  destruct (Nat.eqb_spec m c) as [-> | Hm].
  - rewrite nsum_zero; [reflexivity |]. intros y Hy. destruct (Nat.eqb_spec y c); [lia | reflexivity].
  - rewrite IH by lia. reflexivity.
Qed.

Lemma length_filter_seq n f : length (filter f (seq 0 n)) = nsum n (fun x => ind (f x)).
Proof.
  induction n as [|m IH]; [reflexivity |].
  rewrite seq_S, filter_app, length_app, IH. cbn. destruct (f m); cbn; lia.
Qed.

(** The indices of level k + 1 as a top bit and a low part. *)
Definition cons (k : nat) (b : bool) (y : nat) : nat := if b then (y + Nat.pow 2 k)%nat else y.

Lemma pow2_succ k : Nat.pow 2 (S k) = (Nat.pow 2 k + Nat.pow 2 k)%nat.
Proof. cbn. lia. Qed.

Lemma pow2_pos k : (0 < Nat.pow 2 k)%nat.
Proof. pose proof (Nat.pow_nonzero 2 k ltac:(lia)). lia. Qed.

Lemma cons_lt k b y : (y < Nat.pow 2 k)%nat -> (cons k b y < Nat.pow 2 (S k))%nat.
Proof. intro H. rewrite pow2_succ. unfold cons. destruct b; lia. Qed.

Lemma cons_view k i : (i < Nat.pow 2 (S k))%nat ->
  (i mod Nat.pow 2 k < Nat.pow 2 k)%nat /\ i = cons k (Nat.leb (Nat.pow 2 k) i) (i mod Nat.pow 2 k).
Proof.
  intro Hi. rewrite pow2_succ in Hi. pose proof (pow2_pos k) as Hn.
  split; [apply Nat.mod_upper_bound; lia |]. unfold cons.
  destruct (Nat.leb_spec (Nat.pow 2 k) i) as [L | L].
  - replace i with ((i - Nat.pow 2 k) + 1 * Nat.pow 2 k)%nat at 2 by lia.
    rewrite Nat.Div0.mod_add, Nat.mod_small by lia. lia.
  - rewrite Nat.mod_small by lia. reflexivity.
Qed.

Lemma cons_inj k I J a b : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  cons k I a = cons k J b -> I = J /\ a = b.
Proof. intros Ha Hb E. unfold cons in E. destruct I, J; split; try reflexivity; lia. Qed.

Lemma cons_mod k b y : (y < Nat.pow 2 k)%nat -> cons k b y mod Nat.pow 2 k = y.
Proof.
  intro Hy. pose proof (pow2_pos k). unfold cons. destruct b.
  - replace (y + Nat.pow 2 k)%nat with (y + 1 * Nat.pow 2 k)%nat by lia.
    rewrite Nat.Div0.mod_add. apply Nat.mod_small. exact Hy.
  - apply Nat.mod_small. exact Hy.
Qed.

Lemma cons_top k b y : (y < Nat.pow 2 k)%nat -> Nat.leb (Nat.pow 2 k) (cons k b y) = b.
Proof. intro Hy. unfold cons. destruct b; [apply Nat.leb_le | apply Nat.leb_gt]; lia. Qed.

Lemma nsum_pow_succ k g : nsum (Nat.pow 2 (S k)) g =
  (nsum (Nat.pow 2 k) (fun y => g (cons k false y)) + nsum (Nat.pow 2 k) (fun y => g (cons k true y)))%nat.
Proof.
  rewrite pow2_succ, nsum_shift. f_equal. apply nsum_ext. intros y _. unfold cons. f_equal. lia.
Qed.

Ltac bits := apply Nat.bits_inj; intro; rewrite ?Nat.lxor_spec, ?Nat.bits_0; btauto.

Lemma lxor_cons k A B a b : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  Nat.lxor (cons k A a) (cons k B b) = cons k (xorb A B) (Nat.lxor a b).
Proof.
  intros Ha Hb. unfold cons. destruct A, B; cbn [xorb].
  - apply CdTowerBasisSign.lxor_high_lr; assumption.
  - apply CdTowerBasisSign.lxor_high_l; assumption.
  - rewrite CdTowerBasisSign.lxor_high_r by assumption. rewrite Nat.lxor_comm. reflexivity.
  - reflexivity.
Qed.

(** The invariance of a sum over the indices below 2^k under x -> x XOR c. *)
Lemma nsum_lxor k : forall c g, (c < Nat.pow 2 k)%nat ->
  nsum (Nat.pow 2 k) (fun y => g (Nat.lxor y c)) = nsum (Nat.pow 2 k) g.
Proof.
  induction k as [|k IH]; intros c g Hc.
  - cbn in Hc. assert (c = O) as -> by lia. apply nsum_ext. intros y _. rewrite Nat.lxor_0_r. reflexivity.
  - destruct (cons_view k c Hc) as [Hc' Ec]. revert Ec Hc'.
    generalize (Nat.leb (Nat.pow 2 k) c) (c mod Nat.pow 2 k). intros C c' -> Hc'.
    rewrite (nsum_pow_succ k g), (nsum_pow_succ k (fun y => g (Nat.lxor y (cons k C c')))). cbv beta.
    rewrite (nsum_ext _ (fun y => g (Nat.lxor (cons k false y) (cons k C c')))
      (fun y => g (cons k C (Nat.lxor y c')))) by (intros y Hy; rewrite lxor_cons by assumption; reflexivity).
    rewrite (nsum_ext _ (fun y => g (Nat.lxor (cons k true y) (cons k C c')))
      (fun y => g (cons k (negb C) (Nat.lxor y c')))) by (intros y Hy; rewrite lxor_cons by assumption; reflexivity).
    rewrite (IH c' (fun z => g (cons k C z)) Hc'), (IH c' (fun z => g (cons k (negb C) z)) Hc').
    destruct C; cbn [negb]; lia.
Qed.

(** Index identities of the partner map. *)
Lemma partner_partner i j x : partner i j (partner i j x) = x.
Proof. unfold partner. bits. Qed.

Lemma partner_comm i j x : partner i j x = partner j i x.
Proof. unfold partner. bits. Qed.

Lemma partner_xor i j x : partner i j x = Nat.lxor x (Nat.lxor i j).
Proof. unfold partner. bits. Qed.

Lemma partner_eq_self i j x : partner i j x = x -> i = j.
Proof.
  intro E. apply Nat.lxor_eq.
  replace (Nat.lxor i j) with (Nat.lxor (partner i j x) x) by (unfold partner; bits).
  rewrite E. apply Nat.lxor_nilpotent.
Qed.

Lemma partner_cons k I J X a b y : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat -> (y < Nat.pow 2 k)%nat ->
  partner (cons k I a) (cons k J b) (cons k X y) = cons k (xorb (xorb X I) J) (partner a b y).
Proof.
  intros Ha Hb Hy. unfold partner.
  rewrite (lxor_cons k X I y a Hy Ha), lxor_cons by (try apply CdTowerBasisSign.lxor_lt; assumption).
  reflexivity.
Qed.

Lemma lxor_eqb_move y c z : Nat.eqb (Nat.lxor y c) z = Nat.eqb y (Nat.lxor z c).
Proof.
  destruct (Nat.eqb_spec (Nat.lxor y c) z) as [E | E], (Nat.eqb_spec y (Nat.lxor z c)) as [F | F];
    try reflexivity; exfalso.
  - apply F. subst z. bits.
  - apply E. subst y. bits.
Qed.

Lemma eqb_0_l x : Nat.eqb 0 x = Nat.eqb x 0.
Proof. apply Nat.eqb_sym. Qed.

Lemma partner_eqb_0 a b y : Nat.eqb (partner a b y) 0 = Nat.eqb y (Nat.lxor a b).
Proof. rewrite partner_xor, lxor_eqb_move, Nat.lxor_0_l. reflexivity. Qed.

Lemma eqb_partner_l a b y : Nat.eqb a (partner a b y) = Nat.eqb y b.
Proof.
  rewrite Nat.eqb_sym, partner_xor, lxor_eqb_move.
  replace (Nat.lxor a (Nat.lxor a b)) with b by bits. reflexivity.
Qed.

Lemma eqb_partner_r a b y : Nat.eqb b (partner a b y) = Nat.eqb y a.
Proof.
  rewrite Nat.eqb_sym, partner_xor, lxor_eqb_move.
  replace (Nat.lxor b (Nat.lxor a b)) with a by bits. reflexivity.
Qed.

(** Sign identities. *)
Definition tr (p q : nat) : bool := negb (Nat.eqb p 0) && negb (Nat.eqb q 0) && negb (Nat.eqb p q).

Lemma neg_sign_zero_r k p : neg_sign k p 0 = false.
Proof.
  pose proof (CdTowerBasisSign.sigma_zero_r k p) as Z1.
  destruct (sign_cases k p 0) as [[E S] | [E _]]; [rewrite S in Z1; discriminate | exact E].
Qed.

Lemma neg_sign_self_eq k p : (p < Nat.pow 2 k)%nat -> neg_sign k p p = negb (Nat.eqb p 0).
Proof.
  intro Hp. destruct (Nat.eqb_spec p 0) as [-> | H0].
  - apply neg_sign_zero_l.
  - apply neg_sign_self; assumption.
Qed.

(** Tower.negSign_swap_xor: exchanging the factors reverses the sign
    exactly when both differ from 0 and from each other. *)
Lemma neg_sign_swap_xor k p q : (p < Nat.pow 2 k)%nat -> (q < Nat.pow 2 k)%nat ->
  neg_sign k q p = xorb (neg_sign k p q) (tr p q).
Proof.
  intros Hp Hq. unfold tr.
  destruct (Nat.eqb_spec p 0) as [-> | Hp0]; [rewrite neg_sign_zero_l, neg_sign_zero_r; reflexivity |].
  destruct (Nat.eqb_spec q 0) as [-> | Hq0]; [rewrite neg_sign_zero_l, neg_sign_zero_r; reflexivity |].
  destruct (Nat.eqb_spec p q) as [-> | Hpq]; [destruct (neg_sign k q q); reflexivity |].
  rewrite (neg_sign_swap k p q Hp Hq Hp0 Hq0 Hpq). destruct (neg_sign k p q); reflexivity.
Qed.

Lemma neg_sign_xor_left k p q : (p < Nat.pow 2 k)%nat -> (q < Nat.pow 2 k)%nat ->
  neg_sign k q (Nat.lxor p q) = xorb (negb (Nat.eqb q 0)) (neg_sign k q p).
Proof. intros Hp Hq. rewrite Nat.lxor_comm. apply neg_sign_xor_right; assumption. Qed.

Ltac ltb_simpl k :=
  repeat match goal with
  | H : (?x < Nat.pow 2 k)%nat |- context [Nat.ltb ?x (Nat.pow 2 k)] =>
      rewrite (proj2 (Nat.ltb_lt x (Nat.pow 2 k)) H)
  | |- context [Nat.ltb (?x + Nat.pow 2 k) (Nat.pow 2 k)] =>
      rewrite (proj2 (Nat.ltb_ge (x + Nat.pow 2 k) (Nat.pow 2 k)) (Nat.le_add_l _ _))
  end.

(** Tower.negSign_cons: the sign of level k + 1 from the low parts and
    the top bits. *)
Lemma neg_sign_cons k P Q p q : (p < Nat.pow 2 k)%nat -> (q < Nat.pow 2 k)%nat ->
  neg_sign (S k) (cons k P p) (cons k Q q) =
  xorb (xorb (neg_sign k p q) (P && xorb (negb (Nat.eqb q 0)) Q)) (Q && tr p q).
Proof.
  intros Hp Hq. rewrite neg_sign_unfold. unfold cons.
  destruct P, Q; ltb_simpl k; rewrite ?Nat.add_sub.
  - destruct (Nat.eqb_spec q 0) as [-> | Hq0].
    + unfold tr. rewrite neg_sign_zero_r. destruct (Nat.eqb p 0); reflexivity.
    + rewrite (neg_sign_swap_xor k p q Hp Hq). destruct (neg_sign k p q), (tr p q); reflexivity.
  - destruct (neg_sign k p q), (Nat.eqb q 0); reflexivity.
  - rewrite (neg_sign_swap_xor k p q Hp Hq). destruct (neg_sign k p q), (tr p q); reflexivity.
  - destruct (neg_sign k p q); reflexivity.
Qed.

(** Tower.misaligned: the four signs of the pair {x, partner i j x}
    multiply to -1. *)
Definition misaligned (k i j x : nat) : bool :=
  xorb (xorb (xorb (neg_sign k i x) (neg_sign k i (partner i j x))) (neg_sign k j x))
    (neg_sign k j (partner i j x)).

Lemma aligned_misaligned k i j x :
  orb (aligned_add k i j x) (aligned_sub k i j x) = negb (misaligned k i j x).
Proof.
  unfold aligned_add, aligned_sub, misaligned.
  destruct (neg_sign k i x), (neg_sign k j (partner i j x)), (neg_sign k j x),
    (neg_sign k i (partner i j x)); reflexivity.
Qed.

Lemma misaligned_comm k i j x : misaligned k i j x = misaligned k j i x.
Proof.
  unfold misaligned. rewrite (partner_comm j i).
  destruct (neg_sign k i x), (neg_sign k j (partner i j x)), (neg_sign k j x),
    (neg_sign k i (partner i j x)); reflexivity.
Qed.

Lemma misaligned_partner k i j x : misaligned k i j (partner i j x) = misaligned k i j x.
Proof.
  unfold misaligned. rewrite partner_partner.
  destruct (neg_sign k i x), (neg_sign k j (partner i j x)), (neg_sign k j x),
    (neg_sign k i (partner i j x)); reflexivity.
Qed.

Ltac eqb_norm :=
  rewrite ?Nat.eqb_refl, ?eqb_0_l, ?CdTowerBasisSign.lxor_eqb_0, ?CdTowerBasisSign.lxor_eqb_self,
    ?CdTowerBasisSign.lxor_eqb_self_r.

Ltac close_bool :=
  repeat match goal with |- context [neg_sign ?k ?p ?q] => destruct (neg_sign k p q) end;
  repeat match goal with |- context [Nat.eqb ?x ?y] => destruct (Nat.eqb x y) end;
  reflexivity.

(** The transposition corrections of the four signs of a pair cancel. *)
Lemma transpose_cancel a b y :
  xorb (tr a y) (tr a (partner a b y)) = xorb (tr b y) (tr b (partner a b y)).
Proof.
  unfold tr. rewrite !partner_eqb_0, eqb_partner_l, eqb_partner_r.
  destruct (Nat.eq_dec y 0) as [-> | H0]; [eqb_norm; close_bool |].
  destruct (Nat.eq_dec y a) as [-> | Ha]; [eqb_norm; rewrite ?(Nat.eqb_sym b a); close_bool |].
  destruct (Nat.eq_dec y b) as [-> | Hb]; [eqb_norm; rewrite ?(Nat.eqb_sym b a); close_bool |].
  destruct (Nat.eq_dec y (Nat.lxor a b)) as [-> | Hc]; [eqb_norm; close_bool |].
  rewrite (proj2 (Nat.eqb_neq y 0) H0), (proj2 (Nat.eqb_neq a y) (not_eq_sym Ha)),
    (proj2 (Nat.eqb_neq b y) (not_eq_sym Hb)), (proj2 (Nat.eqb_neq y b) Hb),
    (proj2 (Nat.eqb_neq y a) Ha), (proj2 (Nat.eqb_neq y (Nat.lxor a b)) Hc).
  close_bool.
Qed.

(** For i and j in the same half the corrections cancel. *)
Lemma misaligned_cons_same k I X a b y :
  (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat -> (y < Nat.pow 2 k)%nat ->
  misaligned (S k) (cons k I a) (cons k I b) (cons k X y) = misaligned k a b y.
Proof.
  intros Ha Hb Hy. pose proof (partner_lt k a b y Ha Hb Hy) as Hp. pose proof (transpose_cancel a b y) as Ht.
  unfold misaligned. rewrite partner_cons by assumption.
  replace (xorb (xorb X I) I) with X by (destruct X, I; reflexivity).
  rewrite !neg_sign_cons by assumption.
  revert Ht.
  generalize (neg_sign k a y) (neg_sign k a (partner a b y)) (neg_sign k b y) (neg_sign k b (partner a b y))
    (tr a y) (tr a (partner a b y)) (tr b y) (tr b (partner a b y)) (Nat.eqb y 0) (Nat.eqb (partner a b y) 0).
  intros s1 s2 s3 s4 t1 t2 t3 t4 d1 d2 Ht.
  destruct I, X, s1, s2, s3, s4, t1, t2, t3, t4, d1, d2; cbn in Ht |- *; congruence.
Qed.

(** For i in the first half and j in the second, with nonzero distinct
    low parts, a low index outside {0, a, b, a XOR b} changes its
    alignment. *)
Lemma misaligned_cons_mixed k a b y :
  (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat -> (y < Nat.pow 2 k)%nat ->
  a <> O -> b <> O -> y <> O -> y <> a -> y <> b -> y <> Nat.lxor a b ->
  misaligned (S k) (cons k false a) (cons k true b) (cons k false y) = negb (misaligned k a b y).
Proof.
  intros Ha Hb Hy Ha0 Hb0 Hy0 Hya Hyb Hyc. pose proof (partner_lt k a b y Ha Hb Hy) as Hp.
  unfold misaligned. rewrite partner_cons by assumption. cbn [xorb].
  rewrite !neg_sign_cons by assumption. unfold tr.
  rewrite ?partner_eqb_0, ?eqb_partner_l, ?eqb_partner_r.
  rewrite ?(proj2 (Nat.eqb_neq a 0) Ha0), ?(proj2 (Nat.eqb_neq b 0) Hb0), ?(proj2 (Nat.eqb_neq y 0) Hy0),
    ?(proj2 (Nat.eqb_neq y b) Hyb), ?(proj2 (Nat.eqb_neq y a) Hya), ?(proj2 (Nat.eqb_neq y (Nat.lxor a b)) Hyc),
    ?(proj2 (Nat.eqb_neq a y) (not_eq_sym Hya)), ?(proj2 (Nat.eqb_neq b y) (not_eq_sym Hyb)).
  close_bool.
Qed.

Lemma partner_at_zero a b : partner a b 0 = Nat.lxor a b.
Proof. unfold partner. bits. Qed.
Lemma partner_at_left a b : partner a b a = b.
Proof. unfold partner. bits. Qed.
Lemma partner_at_right a b : partner a b b = a.
Proof. unfold partner. bits. Qed.
Lemma partner_at_xor a b : partner a b (Nat.lxor a b) = 0.
Proof. unfold partner. bits. Qed.

(** For nonzero distinct a and b, the indices 0, a, b and a XOR b are
    aligned at neither level. *)
Lemma misaligned_special k a b y : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  a <> O -> b <> O -> a <> b -> (y = O \/ y = a \/ y = b \/ y = Nat.lxor a b) ->
  misaligned k a b y = true /\
  misaligned (S k) (cons k false a) (cons k true b) (cons k false y) = true.
Proof.
  intros Ha Hb Ha0 Hb0 Hab Hy. pose proof (pow2_pos k) as Hn.
  pose proof (CdTowerBasisSign.lxor_lt k a b Ha Hb) as Hc.
  assert (Hy' : (y < Nat.pow 2 k)%nat) by (destruct Hy as [-> | [-> | [-> | ->]]]; assumption || lia).
  pose proof (partner_lt k a b y Ha Hb Hy') as Hp.
  unfold misaligned. rewrite partner_cons by assumption. cbn [xorb].
  rewrite !neg_sign_cons by assumption.
  destruct Hy as [-> | [-> | [-> | ->]]];
    rewrite ?partner_at_zero, ?partner_at_left, ?partner_at_right, ?partner_at_xor;
    rewrite ?(neg_sign_xor_right k a b Ha Hb), ?(neg_sign_xor_left k a b Ha Hb),
      ?(neg_sign_self_eq k a Ha), ?(neg_sign_self_eq k b Hb), ?neg_sign_zero_r,
      ?(neg_sign_swap_xor k a b Ha Hb);
    unfold tr; eqb_norm;
    rewrite ?(Nat.eqb_sym b a), ?(Nat.eqb_sym (Nat.lxor a b) a), ?(Nat.eqb_sym (Nat.lxor a b) b);
    eqb_norm;
    rewrite ?(proj2 (Nat.eqb_neq a 0) Ha0), ?(proj2 (Nat.eqb_neq b 0) Hb0), ?(proj2 (Nat.eqb_neq a b) Hab);
    destruct (neg_sign k a b); split; reflexivity.
Qed.

(** For i in the first half and j in the second, with low parts a = 0,
    b = 0 or a = b, no low index is aligned at level k + 1. *)
Lemma misaligned_cons_degenerate k a b y :
  (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat -> (y < Nat.pow 2 k)%nat ->
  (a = O \/ b = O \/ a = b) ->
  misaligned (S k) (cons k false a) (cons k true b) (cons k false y) = true.
Proof.
  intros Ha Hb Hy H. pose proof (partner_lt k a b y Ha Hb Hy) as Hp.
  unfold misaligned. rewrite partner_cons by assumption. cbn [xorb].
  rewrite !neg_sign_cons by assumption.
  destruct H as [-> | [-> | <-]].
  - rewrite !neg_sign_zero_l. replace (partner 0 b y) with (Nat.lxor b y) by (unfold partner; bits).
    rewrite (neg_sign_xor_right k b y Hb Hy). unfold tr. eqb_norm.
    destruct (Nat.eq_dec y 0) as [-> | Hy0]; [eqb_norm; close_bool |].
    rewrite (proj2 (Nat.eqb_neq y 0) Hy0).
    destruct (Nat.eq_dec b y) as [<- | Hby]; [rewrite (proj2 (Nat.eqb_neq b 0) Hy0); eqb_norm; close_bool |].
    rewrite ?(proj2 (Nat.eqb_neq b y) Hby). close_bool.
  - rewrite !neg_sign_zero_l. replace (partner a 0 y) with (Nat.lxor a y) by (unfold partner; bits).
    rewrite (neg_sign_xor_right k a y Ha Hy). unfold tr. eqb_norm.
    destruct (Nat.eq_dec y 0) as [-> | Hy0]; [eqb_norm; close_bool |].
    rewrite ?(proj2 (Nat.eqb_neq y 0) Hy0).
    destruct (Nat.eq_dec a y) as [<- | Hay]; [rewrite ?(proj2 (Nat.eqb_neq a 0) Hy0); eqb_norm; close_bool |].
    rewrite ?(proj2 (Nat.eqb_neq a y) Hay). close_bool.
  - replace (partner a a y) with y by (unfold partner; bits). unfold tr. close_bool.
Qed.

(** Counts of aligned indices and of the representatives of aligned pairs. *)
Definition aligned_count (k i j : nat) : nat :=
  nsum (Nat.pow 2 k) (fun x => ind (negb (misaligned k i j x))).

Definition rep_count (k i j : nat) : nat :=
  nsum (Nat.pow 2 k) (fun x => ind (negb (misaligned k i j x) && Nat.ltb x (partner i j x))).

Lemma aligned_pair_count_eq k i j :
  aligned_pair_count k i j = if Nat.eqb i j then O else aligned_count k i j / 2.
Proof.
  unfold aligned_pair_count, aligned_count. destruct (Nat.eqb i j); [reflexivity |].
  rewrite length_filter_seq. f_equal. apply nsum_ext. intros x _. rewrite aligned_misaligned. reflexivity.
Qed.

(** For i <> j the aligned indices are twice the representatives
    x < partner i j x of the aligned pairs. *)
Lemma aligned_count_reps k i j : (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat -> i <> j ->
  aligned_count k i j = (2 * rep_count k i j)%nat.
Proof.
  intros Hi Hj Hij. pose proof (CdTowerBasisSign.lxor_lt k i j Hi Hj) as Hc.
  unfold aligned_count, rep_count.
  rewrite (nsum_ext _ _ (fun x => ind (negb (misaligned k i j x) && Nat.ltb x (partner i j x)) +
    ind (negb (misaligned k i j x) && Nat.ltb (partner i j x) x))%nat).
  - rewrite nsum_add.
    rewrite (nsum_ext _ (fun x => ind (negb (misaligned k i j x) && Nat.ltb (partner i j x) x))
      (fun x => (fun z => ind (negb (misaligned k i j z) && Nat.ltb z (partner i j z))) (Nat.lxor x (Nat.lxor i j)))).
    + pose proof (nsum_lxor k (Nat.lxor i j)
        (fun z => ind (negb (misaligned k i j z) && Nat.ltb z (partner i j z))) Hc) as L.
      cbv beta in L |- *. rewrite L. lia.
    + intros x _. cbv beta. rewrite <- partner_xor, misaligned_partner, partner_partner. reflexivity.
  - intros x _. assert (partner i j x <> x) as Hne by (intro E; apply Hij; exact (partner_eq_self i j x E)).
    destruct (negb (misaligned k i j x)); cbn [andb]; [| reflexivity].
    destruct (Nat.ltb_spec x (partner i j x)), (Nat.ltb_spec (partner i j x) x); cbn; lia.
Qed.

Lemma aligned_count_two_mul k i j : (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat -> i <> j ->
  aligned_count k i j = (2 * aligned_pair_count k i j)%nat.
Proof.
  intros Hi Hj Hij. rewrite aligned_pair_count_eq, (proj2 (Nat.eqb_neq i j) Hij), aligned_count_reps by assumption.
  rewrite Nat.mul_comm, Nat.div_mul by lia. lia.
Qed.

(** The count is the number of representatives, for all i and j. *)
Lemma aligned_pair_count_reps k i j : (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat ->
  aligned_pair_count k i j = rep_count k i j.
Proof.
  intros Hi Hj. destruct (Nat.eq_dec i j) as [<- | Hij].
  - unfold aligned_pair_count. rewrite Nat.eqb_refl. symmetry. apply nsum_zero. intros x _.
    replace (partner i i x) with x by (unfold partner; bits). rewrite Nat.ltb_irrefl.
    destruct (negb (misaligned k i i x)); reflexivity.
  - pose proof (aligned_count_two_mul k i j Hi Hj Hij). pose proof (aligned_count_reps k i j Hi Hj Hij). lia.
Qed.

Lemma aligned_pair_count_comm k i j : aligned_pair_count k i j = aligned_pair_count k j i.
Proof.
  rewrite !aligned_pair_count_eq, Nat.eqb_sym. destruct (Nat.eqb j i); [reflexivity |].
  unfold aligned_count. f_equal. apply nsum_ext. intros x _. rewrite misaligned_comm. reflexivity.
Qed.

Lemma aligned_pair_count_self k i : aligned_pair_count k i i = O.
Proof. unfold aligned_pair_count. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma aligned_count_cons_same k I a b : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  aligned_count (S k) (cons k I a) (cons k I b) = (2 * aligned_count k a b)%nat.
Proof.
  intros Ha Hb. unfold aligned_count. rewrite nsum_pow_succ. cbv beta.
  rewrite !(nsum_ext _ (fun y => ind (negb (misaligned (S k) (cons k I a) (cons k I b) (cons k _ y))))
    (fun y => ind (negb (misaligned k a b y)))) by (intros y Hy; rewrite misaligned_cons_same by assumption; reflexivity).
  lia.
Qed.

Definition low_count (k a b : nat) : nat :=
  nsum (Nat.pow 2 k) (fun y => ind (negb (misaligned (S k) (cons k false a) (cons k true b) (cons k false y)))).

Lemma aligned_count_cons_mixed k a b : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  aligned_count (S k) (cons k false a) (cons k true b) = (2 * low_count k a b)%nat.
Proof.
  intros Ha Hb. pose proof (CdTowerBasisSign.lxor_lt k a b Ha Hb) as Hc.
  unfold aligned_count, low_count. rewrite nsum_pow_succ. cbv beta.
  rewrite (nsum_ext _ (fun y => ind (negb (misaligned (S k) (cons k false a) (cons k true b) (cons k true y))))
    (fun y => (fun z => ind (negb (misaligned (S k) (cons k false a) (cons k true b) (cons k false z))))
      (Nat.lxor y (Nat.lxor a b)))).
  - pose proof (nsum_lxor k (Nat.lxor a b)
      (fun z => ind (negb (misaligned (S k) (cons k false a) (cons k true b) (cons k false z)))) Hc) as L.
    cbv beta in L |- *. rewrite L. lia.
  - intros y Hy. cbv beta.
    rewrite <- (misaligned_partner (S k) (cons k false a) (cons k true b) (cons k true y)), partner_cons
      by assumption.
    rewrite <- partner_xor. reflexivity.
Qed.

Lemma cons_false_true_neq k a b : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  cons k false a <> cons k true b.
Proof. intros Ha Hb E. destruct (cons_inj k false true a b Ha Hb E) as [F _]. discriminate F. Qed.

Lemma aligned_pair_count_false_true_zero k a b : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  (a = O \/ b = O \/ a = b) -> aligned_pair_count (S k) (cons k false a) (cons k true b) = O.
Proof.
  intros Ha Hb H.
  pose proof (aligned_count_two_mul (S k) (cons k false a) (cons k true b) (cons_lt k false a Ha)
    (cons_lt k true b Hb) (cons_false_true_neq k a b Ha Hb)) as E.
  rewrite aligned_count_cons_mixed in E by assumption.
  assert (low_count k a b = O) as Z.
  { apply nsum_zero. intros y Hy. rewrite misaligned_cons_degenerate by assumption. reflexivity. }
  lia.
Qed.

Lemma aligned_pair_count_false_true_add k a b : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  a <> O -> b <> O -> a <> b ->
  (aligned_pair_count (S k) (cons k false a) (cons k true b) + 2 * aligned_pair_count k a b + 4)%nat =
    Nat.pow 2 k.
Proof.
  intros Ha Hb Ha0 Hb0 Hab. pose proof (pow2_pos k) as Hn.
  pose proof (CdTowerBasisSign.lxor_lt k a b Ha Hb) as Hc.
  pose proof (aligned_count_two_mul (S k) (cons k false a) (cons k true b) (cons_lt k false a Ha)
    (cons_lt k true b Hb) (cons_false_true_neq k a b Ha Hb)) as E1.
  rewrite aligned_count_cons_mixed in E1 by assumption.
  pose proof (aligned_count_two_mul k a b Ha Hb Hab) as E2.
  assert (Hsum : (aligned_count k a b + low_count k a b + 4)%nat = Nat.pow 2 k).
  { rewrite <- (nsum_const_one (Nat.pow 2 k)).
    rewrite (nsum_ext _ (fun _ => 1) (fun y =>
      ind (negb (misaligned k a b y)) +
      ind (negb (misaligned (S k) (cons k false a) (cons k true b) (cons k false y))) +
      ind (Nat.eqb y 0) + ind (Nat.eqb y a) + ind (Nat.eqb y b) + ind (Nat.eqb y (Nat.lxor a b)))%nat).
    - rewrite !nsum_add, !nsum_delta by (assumption || lia). unfold aligned_count, low_count. lia.
    - intros y Hy.
      destruct (Nat.eq_dec y 0) as [E | H0]; [| destruct (Nat.eq_dec y a) as [E | Hya];
        [| destruct (Nat.eq_dec y b) as [E | Hyb]; [| destruct (Nat.eq_dec y (Nat.lxor a b)) as [E | Hyc]]]].
      5: { rewrite (misaligned_cons_mixed k a b y) by assumption.
           rewrite (proj2 (Nat.eqb_neq y 0) H0), (proj2 (Nat.eqb_neq y a) Hya), (proj2 (Nat.eqb_neq y b) Hyb),
             (proj2 (Nat.eqb_neq y (Nat.lxor a b)) Hyc).
           destruct (misaligned k a b y); reflexivity. }
      all: destruct (misaligned_special k a b y Ha Hb Ha0 Hb0 Hab ltac:(tauto)) as [M1 M2];
        rewrite M1, M2; subst y; eqb_norm;
        rewrite ?(Nat.eqb_sym b a), ?(Nat.eqb_sym (Nat.lxor a b) a), ?(Nat.eqb_sym (Nat.lxor a b) b);
        eqb_norm;
        rewrite ?(proj2 (Nat.eqb_neq a 0) Ha0), ?(proj2 (Nat.eqb_neq b 0) Hb0), ?(proj2 (Nat.eqb_neq a b) Hab);
        reflexivity. }
  lia.
Qed.

(** Tower.alignedPairCount_succ_of_msb_eq: for i and j in the same half,
    the count of level k + 1 is twice that of the low parts. *)
Theorem aligned_pair_count_succ_of_msb_eq k i j :
  (i < Nat.pow 2 (S k))%nat -> (j < Nat.pow 2 (S k))%nat ->
  Nat.leb (Nat.pow 2 k) i = Nat.leb (Nat.pow 2 k) j ->
  aligned_pair_count (S k) i j =
    (2 * aligned_pair_count k (i mod Nat.pow 2 k) (j mod Nat.pow 2 k))%nat.
Proof.
  intros Hi Hj Hm. destruct (cons_view k i Hi) as [Ha Ei]. destruct (cons_view k j Hj) as [Hb Ej].
  revert Ei Ej Hm Ha Hb.
  generalize (Nat.leb (Nat.pow 2 k) i) (Nat.leb (Nat.pow 2 k) j) (i mod Nat.pow 2 k) (j mod Nat.pow 2 k).
  intros I J a b Ei Ej <- Ha Hb. subst i j.
  destruct (Nat.eq_dec a b) as [<- | Hab]; [rewrite !aligned_pair_count_self; reflexivity |].
  assert (Hij : cons k I a <> cons k I b) by (intro E; apply Hab; exact (proj2 (cons_inj k I I a b Ha Hb E))).
  pose proof (aligned_count_two_mul (S k) _ _ (cons_lt k I a Ha) (cons_lt k I b Hb) Hij) as E1.
  pose proof (aligned_count_two_mul k a b Ha Hb Hab) as E2.
  rewrite aligned_count_cons_same in E1 by assumption. lia.
Qed.

(** Tower.alignedPairCount_succ_eq_zero: for i and j in different halves
    with low parts a = 0, b = 0 or a = b, the count is 0. *)
Theorem aligned_pair_count_succ_eq_zero k i j :
  (i < Nat.pow 2 (S k))%nat -> (j < Nat.pow 2 (S k))%nat ->
  Nat.leb (Nat.pow 2 k) i <> Nat.leb (Nat.pow 2 k) j ->
  (i mod Nat.pow 2 k = O \/ j mod Nat.pow 2 k = O \/ i mod Nat.pow 2 k = j mod Nat.pow 2 k) ->
  aligned_pair_count (S k) i j = O.
Proof.
  intros Hi Hj Hm Hd. destruct (cons_view k i Hi) as [Ha Ei]. destruct (cons_view k j Hj) as [Hb Ej].
  revert Ei Ej Hm Hd Ha Hb.
  generalize (Nat.leb (Nat.pow 2 k) i) (Nat.leb (Nat.pow 2 k) j) (i mod Nat.pow 2 k) (j mod Nat.pow 2 k).
  intros I J a b Ei Ej Hm Hd Ha Hb. subst i j.
  destruct I, J; try (exfalso; apply Hm; reflexivity).
  - rewrite aligned_pair_count_comm. apply aligned_pair_count_false_true_zero; [assumption | assumption |].
    destruct Hd as [H | [H | H]]; [right; left | left |]; auto.
  - apply aligned_pair_count_false_true_zero; assumption.
Qed.

(** Tower.alignedPairCount_succ_add: for i and j in different halves with
    nonzero distinct low parts a and b,
    N (k + 1) i j + 2 * N k a b + 4 = 2^k. *)
Theorem aligned_pair_count_succ_add k i j :
  (i < Nat.pow 2 (S k))%nat -> (j < Nat.pow 2 (S k))%nat ->
  Nat.leb (Nat.pow 2 k) i <> Nat.leb (Nat.pow 2 k) j ->
  i mod Nat.pow 2 k <> O -> j mod Nat.pow 2 k <> O -> i mod Nat.pow 2 k <> j mod Nat.pow 2 k ->
  (aligned_pair_count (S k) i j + 2 * aligned_pair_count k (i mod Nat.pow 2 k) (j mod Nat.pow 2 k) + 4)%nat =
    Nat.pow 2 k.
Proof.
  intros Hi Hj Hm Ha0 Hb0 Hab. destruct (cons_view k i Hi) as [Ha Ei]. destruct (cons_view k j Hj) as [Hb Ej].
  revert Ei Ej Hm Ha0 Hb0 Hab Ha Hb.
  generalize (Nat.leb (Nat.pow 2 k) i) (Nat.leb (Nat.pow 2 k) j) (i mod Nat.pow 2 k) (j mod Nat.pow 2 k).
  intros I J a b Ei Ej Hm Ha0 Hb0 Hab Ha Hb. subst i j.
  destruct I, J; try (exfalso; apply Hm; reflexivity).
  - rewrite aligned_pair_count_comm, (aligned_pair_count_comm k a b).
    apply aligned_pair_count_false_true_add; auto.
  - apply aligned_pair_count_false_true_add; assumption.
Qed.

End TwoTermRecursion.

(** The counts that the Lean module TwoTerm.lean decides at level 5:
    Tower.alignedPairCount_pathion_1_18, _1_24, _1_17, _1_26 and _2_27,
    and Tower.alignedPairCount_sedenion_1_10 at level 4. *)
Example aligned_pair_count_level5 :
  TwoTermRecursion.aligned_pair_count 5 1 18 = 12%nat /\
  TwoTermRecursion.aligned_pair_count 5 1 24 = 12%nat /\
  TwoTermRecursion.aligned_pair_count 5 1 17 = 0%nat /\
  TwoTermRecursion.aligned_pair_count 5 1 26 = 4%nat /\
  TwoTermRecursion.aligned_pair_count 5 2 27 = 4%nat /\
  TwoTermRecursion.aligned_pair_count 4 1 10 = 4%nat.
Proof. vm_compute. repeat split. Qed.

(** The recursion at one pair of each case: 1 and 18 lie in different
    halves of level 5 with nonzero distinct low parts 1 and 2, and
    12 + 2 * 0 + 4 = 16; 1 and 10 lie in the same half of level 5 with
    the level-4 count 4 doubled to 8. *)
Example aligned_pair_count_recursion_instances :
  (TwoTermRecursion.aligned_pair_count 5 1 18 + 2 * TwoTermRecursion.aligned_pair_count 4 1 2 + 4 = 16)%nat /\
  TwoTermRecursion.aligned_pair_count 5 1 10 = (2 * TwoTermRecursion.aligned_pair_count 4 1 10)%nat.
Proof. vm_compute. split; reflexivity. Qed.
