(** Algebraic normal form of the Cayley-Dickson sign rows. A truth table
    f on x < 2^k has ANF coefficient anf_coef k f s on the monomial
    prod_(i in s) x_i, the Moebius transform of f over the submasks t of s,
    anf_inversion recovers f from its coefficients, and anf_unique shows no
    other coefficient table reconstructs f. The left sign row
    f_m(x) = [sigma_k(m, x) = -1] of e_m is am_exponent k x m by am_sign.
    For k >= 2 its ANF has no degree-k term, for k >= 3 the monomial that
    omits x_i has coefficient bit i of m, and every left sign row with
    m <> 0 has degree exactly max(1, k - 1). The right sign row h_m(x) = [sigma_k(x, m) = -1]
    has degree 1 when m is a power of two and max(1, bitlen(m) - 2)
    otherwise, at every level k that holds m. *)

From Stdlib Require Import Arith Lia Btauto.
Require Import CdImaginarySumConference CdTowerBasisSign.
Open Scope nat_scope.

(** Parity of g over x < 2^k, split at the highest index bit. *)
Fixpoint xsum (k : nat) (g : nat -> bool) : bool :=
  match k with
  | O => g O
  | S j => xorb (xsum j g) (xsum j (fun x => g (x + Nat.pow 2 j)))
  end.

(** t is a submask of s: every bit of t is a bit of s. *)
Definition subset (t s : nat) : bool := Nat.eqb (Nat.ldiff t s) 0.

(** ANF coefficient of the monomial prod_(i in s) x_i, the Moebius transform of f. *)
Definition anf_coef (k : nat) (f : nat -> bool) (s : nat) : bool :=
  xsum k (fun t => andb (subset t s) (f t)).

Lemma xsum_ext k : forall g h, (forall x, x < Nat.pow 2 k -> g x = h x) -> xsum k g = xsum k h.
Proof.
  induction k as [|j IH]; intros g h E; simpl.
  - apply E. simpl. lia.
  - pose proof (Nat.pow_nonzero 2 j ltac:(lia)).
    rewrite (IH g h), (IH (fun x => g (x + Nat.pow 2 j)) (fun x => h (x + Nat.pow 2 j))); [reflexivity| |];
      intros x Hx; apply E; simpl; lia.
Qed.

Lemma xsum_xor k : forall g h, xsum k (fun x => xorb (g x) (h x)) = xorb (xsum k g) (xsum k h).
Proof.
  induction k as [|j IH]; intros g h; simpl; [reflexivity|].
  rewrite (IH g h), (IH (fun x => g (x + Nat.pow 2 j)) (fun x => h (x + Nat.pow 2 j))). btauto.
Qed.

Lemma xsum_false k : xsum k (fun _ => false) = false.
Proof. induction k as [|j IH]; simpl; [|rewrite IH]; reflexivity. Qed.

(** An odd count needs k = 0: a constant sums to zero on every k >= 1. *)
Lemma xsum_const j b : xsum (S j) (fun _ => b) = false.
Proof. simpl. apply Bool.xorb_nilpotent. Qed.

Lemma bits_high j t b : t < Nat.pow 2 j -> j <= b -> Nat.testbit t b = false.
Proof.
  intros Ht Hb. destruct (Nat.eq_dec t 0) as [->|Ht0]; [apply Nat.bits_0|].
  apply Nat.bits_above_log2. pose proof (Nat.log2_lt_pow2 t j ltac:(lia)). lia.
Qed.

(** The indicator of p sums to 1 on any filter c that keeps p. *)
Lemma xsum_point k c p : p < Nat.pow 2 k -> xsum k (fun x => andb (c x) (Nat.eqb x p)) = c p.
Proof.
  revert c p. induction k as [|j IH]; intros c p Hp; simpl in *.
  - assert (p = 0) as -> by lia. apply Bool.andb_true_r.
  - pose proof (Nat.pow_nonzero 2 j ltac:(lia)).
    destruct (Nat.ltb_spec p (Nat.pow 2 j)) as [Hl|Hl].
    + rewrite (IH c p Hl), (xsum_ext j _ (fun _ => false)), xsum_false; [apply Bool.xorb_false_r|].
      intros x Hx. replace (Nat.eqb (x + Nat.pow 2 j) p) with false by (symmetry; apply Nat.eqb_neq; lia).
      apply Bool.andb_false_r.
    + rewrite (xsum_ext j (fun x => andb (c x) (Nat.eqb x p)) (fun _ => false)), xsum_false.
      2: { intros x Hx. replace (Nat.eqb x p) with false by (symmetry; apply Nat.eqb_neq; lia).
           apply Bool.andb_false_r. }
      rewrite (xsum_ext j _ (fun x => andb (c (x + Nat.pow 2 j)) (Nat.eqb x (p - Nat.pow 2 j)))).
      * rewrite IH by lia. rewrite Nat.sub_add by lia. reflexivity.
      * intros x Hx. f_equal. destruct (Nat.eqb_spec (x + Nat.pow 2 j) p), (Nat.eqb_spec x (p - Nat.pow 2 j));
          reflexivity || lia.
Qed.

Lemma ldiff_nonzero a b : Nat.testbit a b = true -> Nat.eqb a 0 = false.
Proof. intro H. apply Nat.eqb_neq. intros ->. rewrite Nat.bits_0 in H. discriminate. Qed.

(** Submasks across the highest bit j of a (j + 1)-bit index. *)
Lemma subset_low_high j t s : t < Nat.pow 2 j -> s < Nat.pow 2 j -> subset t (s + Nat.pow 2 j) = subset t s.
Proof.
  intros Ht Hs. unfold subset. rewrite (add_high_bit j s Hs). f_equal. apply Nat.bits_inj. intro b.
  rewrite !Nat.ldiff_spec, Nat.lxor_spec, Nat.pow2_bits_eqb.
  destruct (Nat.eqb_spec j b) as [<-|]; [rewrite (bits_high j t j Ht (le_n j))|]; btauto.
Qed.

Lemma subset_high_low j t s : t < Nat.pow 2 j -> s < Nat.pow 2 j -> subset (t + Nat.pow 2 j) s = false.
Proof.
  intros Ht Hs. unfold subset. rewrite (add_high_bit j t Ht). apply (ldiff_nonzero _ j).
  rewrite Nat.ldiff_spec, Nat.lxor_spec, Nat.pow2_bits_eqb, Nat.eqb_refl, (bits_high j t j Ht (le_n j)),
    (bits_high j s j Hs (le_n j)). reflexivity.
Qed.

Lemma subset_high_high j t s : t < Nat.pow 2 j -> s < Nat.pow 2 j ->
  subset (t + Nat.pow 2 j) (s + Nat.pow 2 j) = subset t s.
Proof.
  intros Ht Hs. unfold subset. rewrite (add_high_bit j t Ht), (add_high_bit j s Hs). f_equal.
  apply Nat.bits_inj. intro b. rewrite !Nat.ldiff_spec, !Nat.lxor_spec, Nat.pow2_bits_eqb.
  destruct (Nat.eqb_spec j b) as [<-|];
    [rewrite (bits_high j t j Ht (le_n j)), (bits_high j s j Hs (le_n j))|]; btauto.
Qed.

(** Coefficients split at the highest bit: a monomial without x_j reads the
    low half, and one with x_j adds the coefficients of both halves. *)
Lemma coef_low j f s : s < Nat.pow 2 j -> anf_coef (S j) f s = anf_coef j f s.
Proof.
  intro Hs. unfold anf_coef. simpl.
  rewrite (xsum_ext j (fun x => andb (subset (x + Nat.pow 2 j) s) (f (x + Nat.pow 2 j))) (fun _ => false)),
    xsum_false; [apply Bool.xorb_false_r|].
  intros x Hx. rewrite subset_high_low by assumption. reflexivity.
Qed.

Lemma coef_high j f s : s < Nat.pow 2 j ->
  anf_coef (S j) f (s + Nat.pow 2 j) = xorb (anf_coef j f s) (anf_coef j (fun x => f (x + Nat.pow 2 j)) s).
Proof.
  intro Hs. unfold anf_coef. simpl. f_equal; apply xsum_ext; intros x Hx.
  - rewrite subset_low_high by assumption. reflexivity.
  - rewrite subset_high_high by assumption. reflexivity.
Qed.

(** Moebius inversion: f is the sum of the monomials its coefficients select,
    so anf_coef is the algebraic normal form. *)
Theorem anf_inversion k : forall f x, x < Nat.pow 2 k ->
  xsum k (fun s => andb (subset s x) (anf_coef k f s)) = f x.
Proof.
  induction k as [|j IH]; intros f x Hx.
  - simpl in Hx. assert (x = 0) as -> by lia. reflexivity.
  - pose proof (Nat.pow_nonzero 2 j ltac:(lia)). simpl.
    destruct (Nat.ltb_spec x (Nat.pow 2 j)) as [Hl|Hl].
    + rewrite (xsum_ext j (fun s => andb (subset (s + Nat.pow 2 j) x) _) (fun _ => false)), xsum_false.
      2: { intros s Hs. rewrite subset_high_low by assumption. reflexivity. }
      rewrite Bool.xorb_false_r, <- (IH f x Hl). apply xsum_ext. intros s Hs. rewrite coef_low by assumption.
      reflexivity.
    + destruct (split_high j x Hx Hl) as [x' [Hx' ->]].
      rewrite (xsum_ext j _ (fun s => andb (subset s x') (anf_coef j f s))).
      2: { intros s Hs. rewrite subset_low_high, coef_low by assumption. reflexivity. }
      rewrite (xsum_ext j (fun s => andb (subset (s + Nat.pow 2 j) (x' + Nat.pow 2 j))
                                     (anf_coef (S j) f (s + Nat.pow 2 j))) (fun s => xorb (andb (subset s x') (anf_coef j f s))
                                       (andb (subset s x') (anf_coef j (fun t => f (t + Nat.pow 2 j)) s)))).
      2: { intros s Hs. rewrite subset_high_high, coef_high by assumption. btauto. }
      rewrite xsum_xor, !IH by assumption. btauto.
Qed.

(** The full monomial and the monomial that omits x_i read plain and
    bit-i-filtered sums. *)
Lemma subset_ones n t : t < Nat.pow 2 n -> subset t (Nat.ones n) = true.
Proof.
  intro Ht. unfold subset. apply Nat.eqb_eq, Nat.bits_inj_0. intro b. rewrite Nat.ldiff_spec.
  destruct (Nat.ltb_spec b n) as [Hb|Hb].
  - rewrite Nat.ones_spec_low by exact Hb. apply Bool.andb_false_r.
  - rewrite (bits_high n t b Ht Hb). reflexivity.
Qed.

Lemma subset_omit n i t : t < Nat.pow 2 n -> i < n ->
  subset t (Nat.lxor (Nat.ones n) (Nat.pow 2 i)) = negb (Nat.testbit t i).
Proof.
  intros Ht Hi. unfold subset. destruct (Nat.testbit t i) eqn:Ti.
  - apply (ldiff_nonzero _ i). rewrite Nat.ldiff_spec, Nat.lxor_spec, Nat.ones_spec_low, Nat.pow2_bits_eqb,
      Nat.eqb_refl, Ti by exact Hi. reflexivity.
  - apply Nat.eqb_eq, Nat.bits_inj_0. intro b. rewrite Nat.ldiff_spec, Nat.lxor_spec, Nat.pow2_bits_eqb.
    destruct (Nat.ltb_spec b n) as [Hb|Hb]; [|rewrite (bits_high n t b Ht Hb); reflexivity].
    rewrite Nat.ones_spec_low by exact Hb.
    destruct (Nat.eqb_spec i b) as [<-|]; [rewrite Ti|]; btauto.
Qed.

Lemma coef_full n f : anf_coef n f (Nat.ones n) = xsum n f.
Proof. apply xsum_ext. intros t Ht. rewrite subset_ones by exact Ht. reflexivity. Qed.

Lemma coef_omit n i f : i < n ->
  anf_coef n f (Nat.lxor (Nat.ones n) (Nat.pow 2 i)) = xsum n (fun x => andb (negb (Nat.testbit x i)) (f x)).
Proof. intro Hi. apply xsum_ext. intros t Ht. rewrite subset_omit by assumption. reflexivity. Qed.

Lemma testbit_high_low j y i : y < Nat.pow 2 j -> i < j -> Nat.testbit (y + Nat.pow 2 j) i = Nat.testbit y i.
Proof.
  intros Hy Hi. rewrite (add_high_bit j y Hy), Nat.lxor_spec, Nat.pow2_bits_eqb.
  replace (Nat.eqb j i) with false by (symmetry; apply Nat.eqb_neq; lia). apply Bool.xorb_false_r.
Qed.

Lemma testbit_high_top j y : y < Nat.pow 2 j -> Nat.testbit (y + Nat.pow 2 j) j = true.
Proof.
  intro Hy. rewrite (add_high_bit j y Hy), Nat.lxor_spec, Nat.pow2_bits_eqb, Nat.eqb_refl,
    (bits_high j y j Hy (le_n j)). reflexivity.
Qed.

(** Half of the indices of a k >= 2 bit range have bit i clear, an even count. *)
Lemma filter_even j i : i < j -> 2 <= j -> xsum j (fun y => negb (Nat.testbit y i)) = false.
Proof.
  intros Hi Hj. destruct j as [|j]; [lia|]. simpl. destruct (Nat.eq_dec i j) as [->|Hij].
  - rewrite (xsum_ext j _ (fun _ => true)), (xsum_ext j (fun y => negb (Nat.testbit (y + Nat.pow 2 j) j)) (fun _ => false)).
    + destruct j as [|j]; [lia|]. rewrite xsum_const, xsum_false. reflexivity.
    + intros y Hy. rewrite testbit_high_top by exact Hy. reflexivity.
    + intros y Hy. rewrite (bits_high j y j Hy (le_n j)). reflexivity.
  - rewrite (xsum_ext j (fun y => negb (Nat.testbit (y + Nat.pow 2 j) i)) (fun y => negb (Nat.testbit y i))).
    + apply Bool.xorb_nilpotent.
    + intros y Hy. rewrite testbit_high_low by (assumption || lia). reflexivity.
Qed.

(** The commutator exponent of Definition 3.2, read off am_altercommutative. *)
Definition alt (a b : nat) : bool := andb (negb (Nat.eqb a 0)) (andb (negb (Nat.eqb b 0)) (negb (Nat.eqb a b))).

Lemma alt_points y m : m <> 0 -> alt y m = xorb true (xorb (Nat.eqb y 0) (Nat.eqb y m)).
Proof.
  intro Hm. unfold alt. rewrite (proj2 (Nat.eqb_neq m 0) Hm).
  destruct (Nat.eqb_spec y 0), (Nat.eqb_spec y m); try (exfalso; lia); reflexivity.
Qed.

Lemma xsum_alt j c m : m < Nat.pow 2 j ->
  xsum j (fun y => andb (c y) (alt y m)) = if Nat.eqb m 0 then false else xorb (xsum j c) (xorb (c 0) (c m)).
Proof.
  intro Hm. destruct (Nat.eqb_spec m 0) as [->|Hm0].
  - rewrite (xsum_ext j _ (fun _ => false)); [apply xsum_false|]. intros y _. unfold alt. rewrite Nat.eqb_refl. btauto.
  - rewrite (xsum_ext j _ (fun y => xorb (c y) (xorb (andb (c y) (Nat.eqb y 0)) (andb (c y) (Nat.eqb y m))))).
    + rewrite !xsum_xor, !xsum_point by (assumption || (pose proof (Nat.pow_nonzero 2 j); lia)). reflexivity.
    + intros y _. rewrite alt_points by exact Hm0. btauto.
Qed.

(** Pairing x with x + 2^j: f_m(y, 0) + f_m(y, 1) is the commutator exponent,
    complemented when m sits in the top half. *)
Lemma row_pair_low j m y : m < Nat.pow 2 j -> y < Nat.pow 2 j ->
  xorb (am_exponent (S j) y m) (am_exponent (S j) (y + Nat.pow 2 j) m) = alt y m.
Proof. intros Hm Hy. rewrite am_ll, am_hl by assumption. apply am_altercommutative; assumption. Qed.

Lemma row_pair_high j m y : m < Nat.pow 2 j -> y < Nat.pow 2 j ->
  xorb (am_exponent (S j) y (m + Nat.pow 2 j)) (am_exponent (S j) (y + Nat.pow 2 j) (m + Nat.pow 2 j)) =
  negb (alt y m).
Proof.
  intros Hm Hy. rewrite am_lh, am_hh by assumption. unfold alt. rewrite <- (am_altercommutative j y m Hy Hm).
  btauto.
Qed.

(** The filtered sum over a filter c that ignores bit j becomes a sum of pairs. *)
Lemma xsum_pairs j c g : (forall y, y < Nat.pow 2 j -> c (y + Nat.pow 2 j) = c y) ->
  xsum (S j) (fun x => andb (c x) (g x)) = xsum j (fun y => andb (c y) (xorb (g y) (g (y + Nat.pow 2 j)))).
Proof.
  intro Hc. simpl. rewrite (xsum_ext j (fun x => andb (c (x + Nat.pow 2 j)) (g (x + Nat.pow 2 j)))
    (fun x => andb (c x) (g (x + Nat.pow 2 j)))) by (intros y Hy; rewrite Hc by exact Hy; reflexivity).
  rewrite <- xsum_xor. apply xsum_ext. intros y _. btauto.
Qed.

(** The left sign row of e_m: f_m(x) = [sigma_k(m, x) = -1] (am_sign). *)
Definition sign_row (k m : nat) (x : nat) : bool := am_exponent k x m.

Lemma sign_row_sigma k m x : m < Nat.pow 2 k -> x < Nat.pow 2 k -> sign_of (sign_row k m x) = sigma k m x.
Proof. intros Hm Hx. apply am_sign; assumption. Qed.

Lemma row_filtered j c m : (forall y, y < Nat.pow 2 j -> c (y + Nat.pow 2 j) = c y) ->
  m < Nat.pow 2 (S j) ->
  xsum (S j) (fun x => andb (c x) (sign_row (S j) m x)) =
  if Nat.ltb m (Nat.pow 2 j) then xsum j (fun y => andb (c y) (alt y m))
  else xorb (xsum j c) (xsum j (fun y => andb (c y) (alt y (m - Nat.pow 2 j)))).
Proof.
  intros Hc Hm. unfold sign_row. rewrite xsum_pairs by exact Hc.
  destruct (Nat.ltb_spec m (Nat.pow 2 j)) as [Hl|Hl].
  - apply xsum_ext. intros y Hy. rewrite row_pair_low by assumption. reflexivity.
  - destruct (split_high j m Hm Hl) as [m' [Hm' ->]]. rewrite Nat.add_sub, <- xsum_xor.
    apply xsum_ext. intros y Hy. rewrite row_pair_high by assumption. btauto.
Qed.

(** Every left sign row of A_k, k >= 2, has even weight: its ANF has no
    degree-k term. *)
Theorem sign_row_top k m : 2 <= k -> m < Nat.pow 2 k -> anf_coef k (sign_row k m) (Nat.ones k) = false.
Proof.
  intros Hk Hm. rewrite coef_full. destruct k as [|j]; [lia|].
  rewrite (xsum_ext (S j) _ (fun x => andb true (sign_row (S j) m x))) by reflexivity.
  rewrite row_filtered by (reflexivity || exact Hm).
  destruct j as [|j]; [lia|].
  destruct (Nat.ltb_spec m (Nat.pow 2 (S j))) as [Hl|Hl].
  - rewrite xsum_alt by exact Hl. rewrite xsum_const. destruct (Nat.eqb m 0); reflexivity.
  - rewrite xsum_alt by (simpl in Hm |- *; lia). rewrite xsum_const.
    destruct (Nat.eqb (m - Nat.pow 2 (S j)) 0); reflexivity.
Qed.

Lemma sign_row_low_bit j m i : 2 <= j -> i < j -> m < Nat.pow 2 (S j) ->
  anf_coef (S j) (sign_row (S j) m) (Nat.lxor (Nat.ones (S j)) (Nat.pow 2 i)) = Nat.testbit m i.
Proof.
  intros Hj Hi Hm. rewrite coef_omit by lia.
  rewrite row_filtered by (assumption || (intros y Hy; rewrite testbit_high_low by assumption; reflexivity)).
  rewrite filter_even by assumption.
  destruct (Nat.ltb_spec m (Nat.pow 2 j)) as [Hl|Hl].
  - rewrite xsum_alt, filter_even by assumption. rewrite Nat.bits_0. destruct (Nat.eqb_spec m 0) as [->|]; [rewrite Nat.bits_0; reflexivity|].
    destruct (Nat.testbit m i); reflexivity.
  - destruct (split_high j m Hm Hl) as [m' [Hm' ->]]. rewrite Nat.add_sub, xsum_alt, testbit_high_low, Nat.bits_0, ?filter_even by assumption.
    destruct (Nat.eqb_spec m' 0) as [->|]; [rewrite Nat.bits_0; reflexivity|].
    destruct (Nat.testbit m' i); reflexivity.
Qed.

Lemma sign_row_top_bit j m : 2 <= j -> m < Nat.pow 2 (S j) ->
  anf_coef (S j) (sign_row (S j) m) (Nat.lxor (Nat.ones (S j)) (Nat.pow 2 j)) = Nat.testbit m j.
Proof.
  intros Hj Hm. rewrite coef_omit by lia. simpl xsum.
  rewrite (xsum_ext j (fun x => andb (negb (Nat.testbit (x + Nat.pow 2 j) j)) _) (fun _ => false)), xsum_false,
    Bool.xorb_false_r.
  2: { intros y Hy. rewrite testbit_high_top by exact Hy. reflexivity. }
  rewrite (xsum_ext j _ (fun y => am_exponent (S j) y m)).
  2: { intros y Hy. rewrite (bits_high j y j Hy (le_n j)). reflexivity. }
  destruct (Nat.ltb_spec m (Nat.pow 2 j)) as [Hl|Hl].
  - rewrite (xsum_ext j _ (fun y => sign_row j m y)) by (intros y Hy; apply am_ll; assumption).
    rewrite <- coef_full, sign_row_top by assumption. rewrite (bits_high j m j Hl (le_n j)). reflexivity.
  - destruct (split_high j m Hm Hl) as [m' [Hm' ->]].
    rewrite (xsum_ext j _ (fun y => xorb (sign_row j m' y) (xorb true (andb true (Nat.eqb y 0))))).
    2: { intros y Hy. rewrite am_lh, am_diagonal by exact Hy. unfold sign_row. btauto. }
    destruct j as [|j]; [lia|].
    rewrite !xsum_xor, <- coef_full, sign_row_top, xsum_const, xsum_point, testbit_high_top by
      (assumption || (pose proof (Nat.pow_nonzero 2 (S j)); lia)).
    reflexivity.
Qed.

(** Theorem 3 of docs/notes/cd_phase_degree.md: for k >= 3 the monomial that
    omits x_i carries coefficient bit i of m. *)
Theorem sign_row_leading k m i : 3 <= k -> m < Nat.pow 2 k -> i < k ->
  anf_coef k (sign_row k m) (Nat.lxor (Nat.ones k) (Nat.pow 2 i)) = Nat.testbit m i.
Proof.
  intros Hk Hm Hi. destruct k as [|j]; [lia|].
  destruct (Nat.eq_dec i j) as [->|Hij].
  - apply sign_row_top_bit; lia.
  - apply sign_row_low_bit; lia.
Qed.

(** Theorem 1 of the same note for k >= 3: the full monomial is absent and the
    monomial omitting x_(log2 m) is present, so deg f_m = k - 1. *)
Theorem sign_row_degree k m : 3 <= k -> 0 < m < Nat.pow 2 k ->
  anf_coef k (sign_row k m) (Nat.ones k) = false /\
  anf_coef k (sign_row k m) (Nat.lxor (Nat.ones k) (Nat.pow 2 (Nat.log2 m))) = true.
Proof.
  intros Hk Hm. split; [apply sign_row_top; lia|].
  rewrite sign_row_leading by (try lia; apply Nat.log2_lt_pow2; lia). apply Nat.bit_log2. lia.
Qed.

(** Monomial weight: the number of variables x_i, i < k, in the monomial s. *)
Fixpoint weight (k s : nat) : nat :=
  match k with
  | O => O
  | S j => weight j s + Nat.b2n (Nat.testbit s j)
  end.

Lemma weight_ext k a b : (forall i, i < k -> Nat.testbit a i = Nat.testbit b i) -> weight k a = weight k b.
Proof.
  induction k as [|j IH]; intro E; simpl; [reflexivity|]. rewrite IH, E by (lia || (intros; apply E; lia)). reflexivity.
Qed.

Lemma weight_low j s : s < Nat.pow 2 j -> weight (S j) s = weight j s.
Proof. intro Hs. simpl. rewrite (bits_high j s j Hs (le_n j)). simpl. lia. Qed.

Lemma weight_high j s : s < Nat.pow 2 j -> weight (S j) (s + Nat.pow 2 j) = S (weight j s).
Proof.
  intro Hs. simpl. rewrite testbit_high_top by exact Hs.
  rewrite (weight_ext j (s + Nat.pow 2 j) s) by (intros i Hi; apply testbit_high_low; assumption). simpl. lia.
Qed.

Lemma weight_zero k : weight k 0 = 0.
Proof. induction k as [|j IH]; simpl; [|rewrite IH, Nat.bits_0]; reflexivity. Qed.

Lemma weight_full k s : weight k s = k -> forall i, i < k -> Nat.testbit s i = true.
Proof.
  induction k as [|j IH]; intros W i Hi; [lia|]. simpl in W.
  assert (weight j s <= j) as Wj.
  { clear IH W Hi. induction j as [|j' IHj]; simpl; [lia|]. destruct (Nat.testbit s j'); simpl; lia. }
  destruct (Nat.testbit s j) eqn:T; simpl in W; [|lia].
  destruct (Nat.eq_dec i j) as [->|]; [exact T|]. apply IH; lia.
Qed.

Lemma weight_le_pred k s : s < Nat.pow 2 k -> s <> Nat.ones k -> weight k s <= k - 1.
Proof.
  intros Hs Hn.
  assert (weight k s <= k) as Wk.
  { clear Hs Hn. induction k as [|j IH]; simpl; [lia|]. destruct (Nat.testbit s j); simpl; lia. }
  destruct (Nat.eq_dec (weight k s) k) as [W|]; [|lia]. exfalso. apply Hn, Nat.bits_inj. intro b.
  destruct (Nat.ltb_spec b k) as [Hb|Hb].
  - rewrite Nat.ones_spec_low by exact Hb. apply (weight_full k s W b Hb).
  - rewrite Nat.ones_spec_high, (bits_high k s b Hs Hb) by exact Hb. reflexivity.
Qed.

Lemma weight_all k s : (forall i, i < k -> Nat.testbit s i = true) -> weight k s = k.
Proof.
  induction k as [|j IH]; intro A; simpl; [reflexivity|]. rewrite IH, A by (lia || (intros; apply A; lia)).
  simpl. lia.
Qed.

Lemma weight_all_but k i s : i < k -> Nat.testbit s i = false ->
  (forall i', i' < k -> i' <> i -> Nat.testbit s i' = true) -> weight k s = k - 1.
Proof.
  revert i. induction k as [|j IH]; intros i Hi F A; [lia|]. simpl.
  destruct (Nat.eq_dec i j) as [->|Hij].
  - rewrite F, weight_all by (intros i' Hi'; apply A; lia). simpl. lia.
  - rewrite A, (IH i) by (try lia; try exact F; intros i' Hi' Hn; apply A; lia). simpl. lia.
Qed.

Lemma weight_omit k i : i < k -> weight k (Nat.lxor (Nat.ones k) (Nat.pow 2 i)) = k - 1.
Proof.
  intro Hi. apply (weight_all_but k i); [exact Hi| |].
  - rewrite Nat.lxor_spec, Nat.ones_spec_low, Nat.pow2_bits_eqb, Nat.eqb_refl by exact Hi. reflexivity.
  - intros i' Hi' Hn. rewrite Nat.lxor_spec, Nat.ones_spec_low, Nat.pow2_bits_eqb by exact Hi'.
    replace (Nat.eqb i i') with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.

Lemma coef_ext k f g s : (forall x, x < Nat.pow 2 k -> f x = g x) -> anf_coef k f s = anf_coef k g s.
Proof. intro E. apply xsum_ext. intros x Hx. rewrite E by exact Hx. reflexivity. Qed.

Lemma coef_xor k f g s : anf_coef k (fun x => xorb (f x) (g x)) s = xorb (anf_coef k f s) (anf_coef k g s).
Proof.
  unfold anf_coef. rewrite <- xsum_xor. apply xsum_ext. intros x _. btauto.
Qed.

(** A constant has the single monomial 1. *)
Lemma coef_const k c s : s < Nat.pow 2 k -> anf_coef k (fun _ => c) s = andb c (Nat.eqb s 0).
Proof.
  revert s. induction k as [|j IH]; intros s Hs.
  - simpl in Hs. assert (s = 0) as -> by lia. unfold anf_coef. simpl. destruct c; reflexivity.
  - destruct (Nat.ltb_spec s (Nat.pow 2 j)) as [Hl|Hl]; [rewrite coef_low, IH by exact Hl; reflexivity|].
    destruct (split_high j s Hs Hl) as [s' [Hs' ->]]. rewrite coef_high, !IH by exact Hs'.
    replace (Nat.eqb (s' + Nat.pow 2 j) 0) with false by (symmetry; apply Nat.eqb_neq, unit_neq_high).
    rewrite Bool.xorb_nilpotent, Bool.andb_false_r. reflexivity.
Qed.

(** The coefficients are unique: the Moebius transform of the function that a
    coefficient table c reconstructs returns c, so anf_coef is the algebraic
    normal form. *)
Definition anf_eval (k : nat) (c : nat -> bool) (x : nat) : bool :=
  xsum k (fun s => andb (subset s x) (c s)).

Lemma anf_eval_low j c x : x < Nat.pow 2 j -> anf_eval (S j) c x = anf_eval j c x.
Proof.
  intro Hx. unfold anf_eval. simpl.
  rewrite (xsum_ext j (fun s => andb (subset (s + Nat.pow 2 j) x) (c (s + Nat.pow 2 j))) (fun _ => false)),
    xsum_false; [apply Bool.xorb_false_r|].
  intros s Hs. rewrite subset_high_low by assumption. reflexivity.
Qed.

Lemma anf_eval_high j c x : x < Nat.pow 2 j ->
  anf_eval (S j) c (x + Nat.pow 2 j) = xorb (anf_eval j c x) (anf_eval j (fun s => c (s + Nat.pow 2 j)) x).
Proof.
  intro Hx. unfold anf_eval. simpl. f_equal; apply xsum_ext; intros s Hs.
  - rewrite subset_low_high by assumption. reflexivity.
  - rewrite subset_high_high by assumption. reflexivity.
Qed.

Theorem anf_unique k : forall c s, s < Nat.pow 2 k -> anf_coef k (anf_eval k c) s = c s.
Proof.
  induction k as [|j IH]; intros c s Hs.
  - simpl in Hs. assert (s = 0) as -> by lia. unfold anf_coef, anf_eval. simpl. destruct (c 0); reflexivity.
  - destruct (Nat.ltb_spec s (Nat.pow 2 j)) as [Hl|Hl].
    + unfold anf_coef. simpl.
      rewrite (xsum_ext j (fun t => andb (subset (t + Nat.pow 2 j) s) _) (fun _ => false)), xsum_false.
      2: { intros t Ht. rewrite subset_high_low by assumption. reflexivity. }
      rewrite Bool.xorb_false_r, <- (IH c s Hl). apply xsum_ext. intros t Ht.
      rewrite anf_eval_low by exact Ht. reflexivity.
    + destruct (split_high j s Hs Hl) as [s' [Hs' ->]]. rewrite coef_high by exact Hs'.
      rewrite (coef_ext j (anf_eval (S j) c) (anf_eval j c)) by (intros t Ht; apply anf_eval_low, Ht).
      rewrite (coef_ext j (fun t => anf_eval (S j) c (t + Nat.pow 2 j))
                (fun t => xorb (anf_eval j c t) (anf_eval j (fun u => c (u + Nat.pow 2 j)) t)))
        by (intros t Ht; apply anf_eval_high, Ht).
      rewrite coef_xor, !IH by exact Hs'. btauto.
Qed.

(** A truth table of exact degree d: every monomial it carries has weight at
    most d, and one of weight d is present. *)
Definition degree_is (k : nat) (f : nat -> bool) (d : nat) : Prop :=
  (forall s, s < Nat.pow 2 k -> anf_coef k f s = true -> weight k s <= d) /\
  (exists s, s < Nat.pow 2 k /\ weight k s = d /\ anf_coef k f s = true).

Lemma omit_lt k i : i < k -> Nat.lxor (Nat.ones k) (Nat.pow 2 i) < Nat.pow 2 k.
Proof.
  intro Hi. pose proof (Nat.pow_nonzero 2 k ltac:(lia)). apply lxor_lt.
  - rewrite Nat.ones_equiv. lia.
  - apply Nat.pow_lt_mono_r; lia.
Qed.

(** Theorem 1 of docs/notes/cd_phase_degree.md for k >= 3, in degree form. *)
Corollary sign_row_degree_is k m : 3 <= k -> 0 < m < Nat.pow 2 k -> degree_is k (sign_row k m) (k - 1).
Proof.
  intros Hk Hm. destruct (sign_row_degree k m Hk Hm) as [Top Lead].
  assert (Nat.log2 m < k) as Hl by (apply Nat.log2_lt_pow2; lia). split.
  - intros s Hs C. apply weight_le_pred; [exact Hs|]. intros ->. congruence.
  - exists (Nat.lxor (Nat.ones k) (Nat.pow 2 (Nat.log2 m))).
    split; [apply omit_lt, Hl|split; [apply weight_omit, Hl|exact Lead]].
Qed.

(** The right sign row of e_m: h_m(x) = [sigma_k(x, m) = -1] (am_sign). *)
Definition right_row (k m : nat) (x : nat) : bool := am_exponent k m x.

Lemma right_row_sigma k m x : m < Nat.pow 2 k -> x < Nat.pow 2 k -> sign_of (right_row k m x) = sigma k x m.
Proof. intros Hm Hx. apply am_sign; assumption. Qed.

(** Proposition 4 of docs/notes/cd_phase_degree.md: degree 1 when m is a
    power of two and max(1, bitlen(m) - 2) otherwise; log2 m - 1 is
    bitlen(m) - 2. *)
Definition right_degree (m : nat) : nat :=
  if Nat.eqb m (Nat.pow 2 (Nat.log2 m)) then 1 else Nat.max 1 (Nat.log2 m - 1).

(** m in the low half: h_m(y, xi) = h'_m(y) + xi, so the top variable adds
    only the monomial x_j. *)
Lemma right_row_lift j m d : 1 <= d -> 0 < m < Nat.pow 2 j ->
  degree_is j (right_row j m) d -> degree_is (S j) (right_row (S j) m) d.
Proof.
  intros Hd Hm [Up [s0 [Hs0 [W0 C0]]]].
  assert (forall s, s < Nat.pow 2 j -> anf_coef (S j) (right_row (S j) m) s = anf_coef j (right_row j m) s) as Low.
  { intros s Hs. rewrite coef_low by exact Hs. apply coef_ext. intros y Hy. apply am_ll; lia. }
  assert (forall s, s < Nat.pow 2 j -> anf_coef (S j) (right_row (S j) m) (s + Nat.pow 2 j) = Nat.eqb s 0) as High.
  { intros s Hs. rewrite coef_high by exact Hs.
    rewrite (coef_ext j (fun x => right_row (S j) m x) (right_row j m)) by (intros y Hy; apply am_ll; lia).
    rewrite (coef_ext j (fun x => right_row (S j) m (x + Nat.pow 2 j)) (fun x => xorb (right_row j m x) true)).
    - rewrite coef_xor, coef_const by exact Hs. btauto.
    - intros y Hy. unfold right_row. rewrite am_lh, am_diagonal by lia.
      replace (Nat.eqb m 0) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity. }
  split.
  - intros s Hs C. destruct (Nat.ltb_spec s (Nat.pow 2 j)) as [Hl|Hl].
    + rewrite weight_low by exact Hl. rewrite Low in C by exact Hl. apply Up; assumption.
    + destruct (split_high j s Hs Hl) as [s' [Hs' ->]]. rewrite High in C by exact Hs'.
      apply Nat.eqb_eq in C. subst s'. rewrite weight_high, weight_zero by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
      exact Hd.
  - exists s0. split; [simpl; lia|]. rewrite weight_low, Low by exact Hs0. split; assumption.
Qed.

(** m = 2^j: h_m(y, xi) = xi. *)
Lemma right_row_power j : degree_is (S j) (right_row (S j) (0 + Nat.pow 2 j)) 1.
Proof.
  pose proof (Nat.pow_nonzero 2 j ltac:(lia)) as Hp.
  assert (forall s, s < Nat.pow 2 j -> anf_coef (S j) (right_row (S j) (0 + Nat.pow 2 j)) s = false) as Low.
  { intros s Hs. rewrite coef_low by exact Hs.
    rewrite (coef_ext j _ (fun _ => false)), coef_const by (exact Hs || (intros y Hy; unfold right_row;
      rewrite am_hl, am_zero_r by exact Hy; reflexivity)). reflexivity. }
  assert (forall s, s < Nat.pow 2 j -> anf_coef (S j) (right_row (S j) (0 + Nat.pow 2 j)) (s + Nat.pow 2 j) =
    Nat.eqb s 0) as High.
  { intros s Hs. rewrite coef_high by exact Hs.
    rewrite (coef_ext j (fun x => right_row (S j) (0 + Nat.pow 2 j) x) (fun _ => false))
      by (intros y Hy; unfold right_row; rewrite am_hl, am_zero_r by exact Hy; reflexivity).
    rewrite (coef_ext j (fun x => right_row (S j) (0 + Nat.pow 2 j) (x + Nat.pow 2 j)) (fun _ => true))
      by (intros y Hy; unfold right_row; rewrite am_hh, am_zero_r, am_zero_l by (exact Hy || lia); reflexivity).
    rewrite !coef_const by exact Hs. reflexivity. }
  split.
  - intros s Hs C. destruct (Nat.ltb_spec s (Nat.pow 2 j)) as [Hl|Hl]; [rewrite Low in C; congruence|].
    destruct (split_high j s Hs Hl) as [s' [Hs' ->]]. rewrite High in C by exact Hs'.
    apply Nat.eqb_eq in C. subst s'. rewrite weight_high, weight_zero by lia. reflexivity.
  - exists (0 + Nat.pow 2 j). split; [simpl; lia|]. rewrite weight_high, weight_zero, High by lia. split; reflexivity.
Qed.

(** m = m' + 2^j with m' <> 0: h_m(y, xi) = f_(m')(y), the left sign row of
    e_(m') one level down, independent of xi. *)
Lemma right_row_top j m' d : 0 < m' < Nat.pow 2 j ->
  degree_is j (sign_row j m') d -> degree_is (S j) (right_row (S j) (m' + Nat.pow 2 j)) d.
Proof.
  intros Hm [Up [s0 [Hs0 [W0 C0]]]].
  assert (forall y, y < Nat.pow 2 j -> right_row (S j) (m' + Nat.pow 2 j) y = sign_row j m' y) as RL.
  { intros y Hy. unfold right_row, sign_row. apply am_hl, Hy. }
  assert (forall y, y < Nat.pow 2 j ->
    right_row (S j) (m' + Nat.pow 2 j) (y + Nat.pow 2 j) = sign_row j m' y) as RH.
  { intros y Hy. unfold right_row, sign_row. rewrite am_hh, am_diagonal by lia.
    replace (Nat.eqb m' 0) with false by (symmetry; apply Nat.eqb_neq; lia). btauto. }
  assert (forall s, s < Nat.pow 2 j -> anf_coef (S j) (right_row (S j) (m' + Nat.pow 2 j)) s =
    anf_coef j (sign_row j m') s) as Low.
  { intros s Hs. rewrite coef_low by exact Hs. apply coef_ext, RL. }
  assert (forall s, s < Nat.pow 2 j ->
    anf_coef (S j) (right_row (S j) (m' + Nat.pow 2 j)) (s + Nat.pow 2 j) = false) as High.
  { intros s Hs. rewrite coef_high by exact Hs. rewrite (coef_ext j _ (sign_row j m')) by exact RL.
    rewrite (coef_ext j (fun x => right_row (S j) (m' + Nat.pow 2 j) (x + Nat.pow 2 j)) (sign_row j m')) by exact RH.
    apply Bool.xorb_nilpotent. }
  split.
  - intros s Hs C. destruct (Nat.ltb_spec s (Nat.pow 2 j)) as [Hl|Hl].
    + rewrite weight_low by exact Hl. rewrite Low in C by exact Hl. apply Up; assumption.
    + destruct (split_high j s Hs Hl) as [s' [Hs' ->]]. rewrite High in C by exact Hs'. discriminate.
  - exists s0. split; [simpl; lia|]. rewrite weight_low, Low by exact Hs0. split; assumption.
Qed.

(** The complex and quaternion sign rows are affine and nonconstant. *)
Lemma sign_row_small j m : 1 <= j <= 2 -> 0 < m < Nat.pow 2 j -> degree_is j (sign_row j m) 1.
Proof.
  intros Hj Hm. destruct j as [|[|[|j]]]; try lia; simpl in Hm; split.
  - intros s Hs _. destruct s as [|[|s]]; simpl in Hs |- *; lia.
  - assert (m = 1) as -> by lia. exists 1. split; [simpl; lia|split; reflexivity].
  - intros s Hs C. destruct s as [|[|[|[|s]]]]; simpl in Hs; try lia; try (simpl; lia).
    destruct m as [|[|[|[|m]]]]; try lia; cbv in C; discriminate C.
  - destruct m as [|[|[|[|m]]]]; try lia; [exists 1|exists 1|exists 2]; split; (simpl; lia) || split; reflexivity.
Qed.

Lemma sign_row_degree_all j m : 1 <= j -> 0 < m < Nat.pow 2 j -> degree_is j (sign_row j m) (Nat.max 1 (j - 1)).
Proof.
  intros Hj Hm. destruct (Nat.le_gt_cases j 2) as [Hs|Hl].
  - replace (Nat.max 1 (j - 1)) with 1 by lia. apply sign_row_small; lia.
  - replace (Nat.max 1 (j - 1)) with (j - 1) by lia. apply sign_row_degree_is; lia.
Qed.

(** Proposition 4 of docs/notes/cd_phase_degree.md for every k: the right sign
    row of e_m has degree 1 when m is a power of two and
    max(1, bitlen(m) - 2) otherwise, independent of k. *)
Theorem right_row_degree k m : 0 < m < Nat.pow 2 k -> degree_is k (right_row k m) (right_degree m).
Proof.
  revert m. induction k as [|j IH]; intros m Hm; [simpl in Hm; lia|].
  destruct (Nat.ltb_spec m (Nat.pow 2 j)) as [Hl|Hl].
  - apply right_row_lift; [unfold right_degree; destruct (Nat.eqb _ _); lia|lia|apply IH; lia].
  - destruct (split_high j m ltac:(lia) Hl) as [m' [Hm' ->]].
    assert (Nat.log2 (m' + Nat.pow 2 j) = j) as L by (apply Nat.log2_unique; simpl in *; lia).
    unfold right_degree. rewrite L. destruct (Nat.eq_dec m' 0) as [->|Hm0].
    + rewrite Nat.eqb_refl. apply right_row_power.
    + replace (Nat.eqb (m' + Nat.pow 2 j) (Nat.pow 2 j)) with false by (symmetry; apply Nat.eqb_neq; lia).
      assert (1 <= j) by (destruct j; simpl in Hm'; lia).
      apply right_row_top; [lia|]. apply sign_row_degree_all; lia.
Qed.
