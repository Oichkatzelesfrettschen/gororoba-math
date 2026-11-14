(** Algebraic degree of the Cayley-Dickson associator phases. For basis
    units e_p, e_q of the tower, W = L_(e_p e_q)^dagger L_(e_p) L_(e_q) is
    diagonal with entry (-1)^g(x) on e_x, where
    g_(p,q)(x) = phi(q, x) + phi(p, q XOR x) + phi(p XOR q, x) + phi(p, q)
    and phi(a, b) = [sigma_k(a, b) = -1] is am_exponent k b a (am_sign);
    equivalently e_p (e_q e_x) = (-1)^g(x) (e_p e_q) e_x. The phases vanish
    when p = 0, q = 0 or p = q and on the whole quaternion level, and for
    k >= 3 and distinct nonzero p, q < 2^k the ANF degree of g_(p,q) is
    max(1, bitlen(max(p, q)) - 2), independent of k. Splitting x at the
    highest index bit, x = (y, xi), every phase is g(y) + c xi with
    c = [p' <> 0] + [q' <> 0] + [p' XOR q' <> 0] read on the low halves.
    A pair inside the low half keeps the phase one level down plus xi; a
    pair reaching the top half adds two distinct point indicators to the
    phase of its low halves, of degree k - 2, which the lower phase cannot
    cancel. *)

From Stdlib Require Import ZArith Lia Btauto.
Require Import CdImaginarySumConference CdTowerBasisSign CdSignRowAnf.
Open Scope nat_scope.

(** The associator phase of W = L_(e_p e_q)^dagger L_(e_p) L_(e_q) at e_x. *)
Definition assoc (k p q x : nat) : bool :=
  xorb (am_exponent k x q)
    (xorb (am_exponent k (Nat.lxor q x) p) (xorb (am_exponent k x (Nat.lxor p q)) (am_exponent k q p))).

Lemma sign_of_xorb a b : sign_of (xorb a b) = (sign_of a * sign_of b)%Z.
Proof. destruct a, b; reflexivity. Qed.

(** The four cd_sign factors of predict.associator_phase. *)
Theorem assoc_sigma k p q x : p < Nat.pow 2 k -> q < Nat.pow 2 k -> x < Nat.pow 2 k ->
  sign_of (assoc k p q x) = (sigma k p q * sigma k (Nat.lxor p q) x * sigma k q x * sigma k p (Nat.lxor q x))%Z.
Proof.
  intros Hp Hq Hx. unfold assoc. rewrite !sign_of_xorb, !am_sign by (try apply lxor_lt; assumption). ring.
Qed.

Lemma scale_scale k : forall r s v, scale k r (scale k s v) = scale k (r * s)%Z v.
Proof. intros r s v. apply ext. intros i _. rewrite !coord_scale. ring. Qed.

(** e_p (e_q e_x) = (-1)^g(x) (e_p e_q) e_x on the tower. *)
Theorem assoc_basis k p q x : p < Nat.pow 2 k -> q < Nat.pow 2 k -> x < Nat.pow 2 k ->
  mul k (basis k p) (mul k (basis k q) (basis k x)) =
  scale k (sign_of (assoc k p q x)) (mul k (mul k (basis k p) (basis k q)) (basis k x)).
Proof.
  intros Hp Hq Hx.
  rewrite (basis_mul k q x Hq Hx), mul_scale_r, (basis_mul k p (Nat.lxor q x) Hp (lxor_lt k q x Hq Hx)), scale_scale.
  rewrite (basis_mul k p q Hp Hq), mul_scale_l, (basis_mul k (Nat.lxor p q) x (lxor_lt k p q Hp Hq) Hx),
    !scale_scale, Nat.lxor_assoc.
  f_equal. rewrite assoc_sigma by assumption.
  rewrite <- (am_sign k x q), <- (am_sign k (Nat.lxor q x) p), <- (am_sign k q p), <- (am_sign k x (Nat.lxor p q))
    by (try apply lxor_lt; assumption).
  destruct (am_exponent k x q), (am_exponent k (Nat.lxor q x) p), (am_exponent k q p),
    (am_exponent k x (Nat.lxor p q)); reflexivity.
Qed.

(** W is the identity when p = 0, q = 0 or p = q. *)
Theorem assoc_degenerate k p q x : p < Nat.pow 2 k -> q < Nat.pow 2 k -> x < Nat.pow 2 k ->
  p = 0 \/ q = 0 \/ p = q -> assoc k p q x = false.
Proof.
  intros Hp Hq Hx [-> | [-> | <-]]; unfold assoc.
  - rewrite Nat.lxor_0_l, !am_zero_r by (try apply lxor_lt; assumption). btauto.
  - rewrite Nat.lxor_0_l, Nat.lxor_0_r, am_zero_r, am_zero_l by assumption. btauto.
  - rewrite Nat.lxor_nilpotent, am_zero_r, am_diagonal by assumption.
    pose proof (am_left_involution k p x Hp Hx) as L. revert L.
    destruct (am_exponent k x p), (am_exponent k (Nat.lxor p x) p), (Nat.eqb p 0); cbn; congruence.
Qed.

(** The quaternions are associative: every phase vanishes at k = 2. *)
Theorem assoc_quaternion p q x : p < 4 -> q < 4 -> x < 4 -> assoc 2 p q x = false.
Proof.
  intros Hp Hq Hx.
  destruct p as [|[|[|[|p]]]], q as [|[|[|[|q]]]], x as [|[|[|[|x]]]]; try lia; reflexivity.
Qed.

(** Slices of the phase at the highest index bit n of level n + 1. *)
Lemma assoc_low n p q y : p < Nat.pow 2 n -> q < Nat.pow 2 n -> y < Nat.pow 2 n ->
  assoc (S n) p q y = assoc n p q y.
Proof. intros Hp Hq Hy. unfold assoc. rewrite !am_ll by (try apply lxor_lt; assumption). reflexivity. Qed.

Lemma alt_sym a b : alt a b = alt b a.
Proof. unfold alt. rewrite (Nat.eqb_sym a b). btauto. Qed.

(** The commutator exponent of a and b is [a <> 0] + [b = 0] + [b = a]. *)
Lemma alt_delta a b : alt a b = xorb (negb (Nat.eqb a 0)) (xorb (Nat.eqb b 0) (Nat.eqb b a)).
Proof.
  unfold alt. destruct (Nat.eqb_spec a 0), (Nat.eqb_spec b 0), (Nat.eqb_spec a b), (Nat.eqb_spec b a);
    try (exfalso; lia); reflexivity.
Qed.

Lemma eqb_lxor a b c : Nat.eqb (Nat.lxor a b) c = Nat.eqb b (Nat.lxor a c).
Proof.
  destruct (Nat.eqb_spec (Nat.lxor a b) c) as [E|E], (Nat.eqb_spec b (Nat.lxor a c)) as [F|F];
    try reflexivity; exfalso.
  - apply F. subst c. bits.
  - apply E. subst b. bits.
Qed.

Lemma am_swap k a b : a < Nat.pow 2 k -> b < Nat.pow 2 k ->
  am_exponent k a b = xorb (am_exponent k b a) (alt a b).
Proof. intros Ha Hb. unfold alt. rewrite <- (am_altercommutative k a b Ha Hb). btauto. Qed.

(** The constant c(p, q) = [p <> 0] + [q <> 0] + [p XOR q <> 0]. *)
Definition cst (p q : nat) : bool :=
  xorb (negb (Nat.eqb p 0)) (xorb (negb (Nat.eqb q 0)) (negb (Nat.eqb (Nat.lxor p q) 0))).

(** The point indicators of the three commutator exponents cancel in pairs. *)
Lemma alt_triple p q y :
  xorb (alt y q) (xorb (alt (Nat.lxor q y) p) (alt y (Nat.lxor p q))) = cst p q.
Proof.
  rewrite (alt_sym y q), (alt_sym (Nat.lxor q y) p), (alt_sym y (Nat.lxor p q)), !alt_delta. unfold cst.
  rewrite !eqb_lxor, !Nat.lxor_0_r, (Nat.lxor_comm q p). btauto.
Qed.

Lemma row_hi_low n m y : m < Nat.pow 2 n -> y < Nat.pow 2 n ->
  am_exponent (S n) (y + Nat.pow 2 n) m = xorb (am_exponent (S n) y m) (alt y m).
Proof. intros Hm Hy. rewrite <- (row_pair_low n m y Hm Hy). btauto. Qed.

Lemma row_hi_high n m y : m < Nat.pow 2 n -> y < Nat.pow 2 n ->
  am_exponent (S n) (y + Nat.pow 2 n) (m + Nat.pow 2 n) =
  xorb (am_exponent (S n) y (m + Nat.pow 2 n)) (negb (alt y m)).
Proof. intros Hm Hy. rewrite <- (row_pair_high n m y Hm Hy). btauto. Qed.

(** Setting the top bit of x adds the constant c of the low halves of p and q. *)
Lemma assoc_high_ll n p q y : p < Nat.pow 2 n -> q < Nat.pow 2 n -> y < Nat.pow 2 n ->
  assoc (S n) p q (y + Nat.pow 2 n) = xorb (assoc (S n) p q y) (cst p q).
Proof.
  intros Hp Hq Hy. unfold assoc. rewrite (lxor_high_r n q y Hq Hy).
  rewrite (row_hi_low n q y), (row_hi_low n p (Nat.lxor y q)), (row_hi_low n (Nat.lxor p q) y)
    by (try apply lxor_lt; assumption).
  rewrite (Nat.lxor_comm y q), <- (alt_triple p q y). btauto.
Qed.

Lemma assoc_high_lh n p q y : p < Nat.pow 2 n -> q < Nat.pow 2 n -> y < Nat.pow 2 n ->
  assoc (S n) p (q + Nat.pow 2 n) (y + Nat.pow 2 n) = xorb (assoc (S n) p (q + Nat.pow 2 n) y) (cst p q).
Proof.
  intros Hp Hq Hy. unfold assoc.
  rewrite (lxor_high_lr n q y Hq Hy), (lxor_high_l n q y Hq Hy), (lxor_high_r n p q Hp Hq).
  rewrite (row_hi_high n q y), (row_hi_low n p (Nat.lxor q y)), (row_hi_high n (Nat.lxor q p) y)
    by (try apply lxor_lt; assumption).
  rewrite (Nat.lxor_comm q p), <- (alt_triple p q y). btauto.
Qed.

Lemma assoc_high_hl n p q y : p < Nat.pow 2 n -> q < Nat.pow 2 n -> y < Nat.pow 2 n ->
  assoc (S n) (p + Nat.pow 2 n) q (y + Nat.pow 2 n) = xorb (assoc (S n) (p + Nat.pow 2 n) q y) (cst p q).
Proof.
  intros Hp Hq Hy. unfold assoc. rewrite (lxor_high_r n q y Hq Hy), (lxor_high_l n p q Hp Hq).
  rewrite (row_hi_low n q y), (row_hi_high n p (Nat.lxor y q)), (row_hi_high n (Nat.lxor p q) y)
    by (try apply lxor_lt; assumption).
  rewrite (Nat.lxor_comm y q), <- (alt_triple p q y). btauto.
Qed.

Lemma assoc_high_hh n p q y : p < Nat.pow 2 n -> q < Nat.pow 2 n -> y < Nat.pow 2 n ->
  assoc (S n) (p + Nat.pow 2 n) (q + Nat.pow 2 n) (y + Nat.pow 2 n) =
  xorb (assoc (S n) (p + Nat.pow 2 n) (q + Nat.pow 2 n) y) (cst p q).
Proof.
  intros Hp Hq Hy. unfold assoc.
  rewrite (lxor_high_lr n q y Hq Hy), (lxor_high_l n q y Hq Hy), (lxor_high_lr n p q Hp Hq).
  rewrite (row_hi_high n q y), (row_hi_high n p (Nat.lxor q y)), (row_hi_low n (Nat.lxor p q) y)
    by (try apply lxor_lt; assumption).
  rewrite <- (alt_triple p q y). btauto.
Qed.

(** With the top bit of x clear, a pair reaching the top half reads the phase
    of its low halves plus commutator and norm terms. *)
Lemma assoc_lh_low n p q y : p < Nat.pow 2 n -> q < Nat.pow 2 n -> y < Nat.pow 2 n ->
  assoc (S n) p (q + Nat.pow 2 n) y = xorb (assoc n p q y) (xorb (alt p (Nat.lxor q y)) (alt p q)).
Proof.
  intros Hp Hq Hy. unfold assoc.
  rewrite (lxor_high_l n q y Hq Hy), (lxor_high_r n p q Hp Hq), am_lh, am_hl, am_lh, am_hl
    by (try apply lxor_lt; assumption).
  rewrite (am_swap n p (Nat.lxor q y)), (am_swap n p q), (Nat.lxor_comm q p) by (try apply lxor_lt; assumption).
  btauto.
Qed.

Lemma assoc_hl_low n p q y : p < Nat.pow 2 n -> q < Nat.pow 2 n -> y < Nat.pow 2 n ->
  assoc (S n) (p + Nat.pow 2 n) q y =
  xorb (assoc n p q y)
    (xorb (negb (Nat.eqb (Nat.lxor q y) 0)) (xorb (negb (Nat.eqb y 0)) (negb (Nat.eqb q 0)))).
Proof.
  intros Hp Hq Hy. unfold assoc.
  rewrite (lxor_high_l n p q Hp Hq), am_ll, !am_lh, !am_diagonal by (try apply lxor_lt; assumption).
  btauto.
Qed.

Lemma assoc_hh_low n p q y : p < Nat.pow 2 n -> q < Nat.pow 2 n -> y < Nat.pow 2 n ->
  assoc (S n) (p + Nat.pow 2 n) (q + Nat.pow 2 n) y =
  xorb (assoc n p q y)
    (xorb (alt p (Nat.lxor q y))
       (xorb (alt p q)
          (xorb (negb (Nat.eqb y 0)) (xorb (negb (Nat.eqb (Nat.lxor q y) 0)) (negb (Nat.eqb q 0)))))).
Proof.
  intros Hp Hq Hy. unfold assoc.
  rewrite (lxor_high_l n q y Hq Hy), (lxor_high_lr n p q Hp Hq), am_lh, !am_hh, am_ll, !am_diagonal
    by (try apply lxor_lt; assumption).
  rewrite (am_swap n p (Nat.lxor q y)), (am_swap n p q) by (try apply lxor_lt; assumption).
  btauto.
Qed.

(** Degree bounds: every monomial of f has weight at most d. *)
Definition deg_le (k : nat) (f : nat -> bool) (d : nat) : Prop :=
  forall s, s < Nat.pow 2 k -> anf_coef k f s = true -> weight k s <= d.

Lemma deg_le_xor k f g d : deg_le k f d -> deg_le k g d -> deg_le k (fun x => xorb (f x) (g x)) d.
Proof.
  intros F G s Hs C. rewrite coef_xor in C. destruct (anf_coef k f s) eqn:E; [apply F; assumption|].
  apply G; [exact Hs|exact C].
Qed.

Lemma deg_le_const k c d : deg_le k (fun _ => c) d.
Proof.
  intros s Hs C. rewrite coef_const in C by exact Hs. destruct c; [|discriminate].
  apply Nat.eqb_eq in C. subst s. rewrite weight_zero. lia.
Qed.

Lemma deg_le_zero k f d : (forall x, x < Nat.pow 2 k -> f x = false) -> deg_le k f d.
Proof. intros Z s Hs C. rewrite (coef_ext k f (fun _ => false)) in C by exact Z. apply (deg_le_const k false d s Hs C). Qed.

Lemma deg_le_mono k f d e : d <= e -> deg_le k f d -> deg_le k f e.
Proof. intros Hde F s Hs C. specialize (F s Hs C). lia. Qed.

Lemma degree_ext k f g d : (forall x, x < Nat.pow 2 k -> f x = g x) -> degree_is k f d -> degree_is k g d.
Proof.
  intros E [Up [s0 [Hs0 [W0 C0]]]].
  assert (forall s, anf_coef k g s = anf_coef k f s) as G by (intro s; symmetry; apply coef_ext, E).
  split; [intros s Hs C; rewrite G in C; apply Up; assumption|].
  exists s0. rewrite G. auto.
Qed.

(** Adding terms of lower degree keeps the exact degree. *)
Lemma degree_xor_lower k F G d e : e < d -> degree_is k F d -> deg_le k G e ->
  degree_is k (fun x => xorb (F x) (G x)) d.
Proof.
  intros He [Up [s0 [Hs0 [W0 C0]]]] UG. split.
  - intros s Hs C. rewrite coef_xor in C. destruct (anf_coef k F s) eqn:E; [apply Up; assumption|].
    specialize (UG s Hs C). lia.
  - exists s0. split; [exact Hs0|split; [exact W0|]]. rewrite coef_xor, C0.
    destruct (anf_coef k G s0) eqn:E; [|reflexivity]. specialize (UG s0 Hs0 E). lia.
Qed.

(** The indicator of p has coefficient [p within s] on the monomial s. *)
Lemma coef_point k p s : p < Nat.pow 2 k -> anf_coef k (fun y => Nat.eqb y p) s = subset p s.
Proof. intro Hp. apply (xsum_point k (fun t => subset t s) p Hp). Qed.

(** Lemma B of docs/notes/cd_phase_degree.md: two distinct point indicators
    sum to degree exactly k - 1. *)
Lemma two_point k u v : 1 <= k -> u < Nat.pow 2 k -> v < Nat.pow 2 k -> u <> v ->
  degree_is k (fun y => xorb (Nat.eqb y u) (Nat.eqb y v)) (k - 1).
Proof.
  intros Hk Hu Hv Huv.
  assert (forall s, anf_coef k (fun y => xorb (Nat.eqb y u) (Nat.eqb y v)) s = xorb (subset u s) (subset v s)) as Coef.
  { intro s. rewrite coef_xor, !coef_point by assumption. reflexivity. }
  split.
  - intros s Hs C. rewrite Coef in C. apply weight_le_pred; [exact Hs|]. intros ->.
    rewrite !subset_ones in C by assumption. discriminate.
  - assert (Nat.lxor u v <> 0) as H0 by (intro E; apply Huv, Nat.lxor_eq, E).
    assert (Nat.log2 (Nat.lxor u v) < k) as Ht by (apply Nat.log2_lt_pow2; [lia|apply lxor_lt; assumption]).
    pose proof (Nat.bit_log2 _ H0) as Tb. rewrite Nat.lxor_spec in Tb.
    exists (Nat.lxor (Nat.ones k) (Nat.pow 2 (Nat.log2 (Nat.lxor u v)))).
    split; [apply omit_lt, Ht|split; [apply weight_omit, Ht|]].
    rewrite Coef, !subset_omit by assumption.
    destruct (Nat.testbit u _), (Nat.testbit v _); cbn in *; congruence.
Qed.

(** A pair reaching the top half: two point indicators over a lower phase. *)
Lemma upper_degree n g G u v c0 : 2 <= n -> u < Nat.pow 2 n -> v < Nat.pow 2 n -> u <> v ->
  deg_le n G (n - 2) ->
  (forall y, y < Nat.pow 2 n -> g y = xorb (G y) (xorb (Nat.eqb y u) (xorb (Nat.eqb y v) c0))) ->
  degree_is n g (n - 1).
Proof.
  intros Hn Hu Hv Huv HG E.
  apply (degree_ext n (fun y => xorb (xorb (Nat.eqb y u) (Nat.eqb y v)) (xorb (G y) c0))).
  - intros y Hy. rewrite E by exact Hy. btauto.
  - apply (degree_xor_lower n _ _ (n - 1) (n - 2)); [lia|apply two_point; (lia || assumption)|].
    apply deg_le_xor; [exact HG|apply deg_le_const].
Qed.

(** A phase whose top variable enters as g(y, xi) = A(y) + c xi keeps the
    degree of A, since xi adds at most the monomial x_n. *)
Lemma lift n g A c d : 1 <= d -> degree_is n A d -> (forall y, y < Nat.pow 2 n -> g y = A y) ->
  (forall y, y < Nat.pow 2 n -> g (y + Nat.pow 2 n) = xorb (g y) c) -> degree_is (S n) g d.
Proof.
  intros Hd [Up [s0 [Hs0 [W0 C0]]]] EL EH.
  assert (forall s, s < Nat.pow 2 n -> anf_coef (S n) g s = anf_coef n A s) as Low.
  { intros s Hs. rewrite coef_low by exact Hs. apply coef_ext, EL. }
  assert (forall s, s < Nat.pow 2 n -> anf_coef (S n) g (s + Nat.pow 2 n) = andb c (Nat.eqb s 0)) as High.
  { intros s Hs. rewrite coef_high by exact Hs.
    rewrite (coef_ext n (fun x => g (x + Nat.pow 2 n)) (fun x => xorb (g x) c)) by exact EH.
    rewrite coef_xor, coef_const by exact Hs. btauto. }
  split.
  - intros s Hs C. destruct (Nat.ltb_spec s (Nat.pow 2 n)) as [Hl|Hl].
    + rewrite weight_low by exact Hl. rewrite Low in C by exact Hl. apply Up; assumption.
    + destruct (split_high n s Hs Hl) as [s' [Hs' ->]]. rewrite High in C by exact Hs'.
      apply andb_prop in C. destruct C as [_ C]. apply Nat.eqb_eq in C. subst s'.
      rewrite weight_high, weight_zero by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia). exact Hd.
  - exists s0. split; [simpl; lia|]. rewrite weight_low, Low by exact Hs0. split; assumption.
Qed.

(** g(y, xi) = xi has degree 1. *)
Lemma lift_zero n g : (forall y, y < Nat.pow 2 n -> g y = false) ->
  (forall y, y < Nat.pow 2 n -> g (y + Nat.pow 2 n) = true) -> degree_is (S n) g 1.
Proof.
  intros EL EH. pose proof (Nat.pow_nonzero 2 n ltac:(lia)) as Hp.
  assert (forall s, s < Nat.pow 2 n -> anf_coef (S n) g s = false) as Low.
  { intros s Hs. rewrite coef_low by exact Hs. rewrite (coef_ext n g (fun _ => false)), coef_const by assumption.
    reflexivity. }
  assert (forall s, s < Nat.pow 2 n -> anf_coef (S n) g (s + Nat.pow 2 n) = Nat.eqb s 0) as High.
  { intros s Hs. rewrite coef_high by exact Hs.
    rewrite (coef_ext n g (fun _ => false)), (coef_ext n (fun x => g (x + Nat.pow 2 n)) (fun _ => true)),
      !coef_const by assumption. reflexivity. }
  split.
  - intros s Hs C. destruct (Nat.ltb_spec s (Nat.pow 2 n)) as [Hl|Hl]; [rewrite Low in C; congruence|].
    destruct (split_high n s Hs Hl) as [s' [Hs' ->]]. rewrite High in C by exact Hs'.
    apply Nat.eqb_eq in C. subst s'. rewrite weight_high, weight_zero by lia. reflexivity.
  - exists (0 + Nat.pow 2 n). split; [simpl; lia|]. rewrite weight_high, weight_zero, High by lia.
    split; reflexivity.
Qed.

(** Theorem 2 of docs/notes/cd_phase_degree.md: max(1, bitlen(max(p, q)) - 2),
    with log2 m - 1 = bitlen(m) - 2. *)
Definition assoc_degree (p q : nat) : nat := Nat.max 1 (Nat.log2 (Nat.max p q) - 1).

Lemma max_bounds p q b : 0 < p -> 0 < q -> p < b -> q < b -> 0 < Nat.max p q < b.
Proof. intros. destruct (Nat.max_spec p q) as [[_ ->]|[_ ->]]; lia. Qed.

Theorem assoc_degree_is k p q : 3 <= k -> p < Nat.pow 2 k -> q < Nat.pow 2 k -> p <> 0 -> q <> 0 -> p <> q ->
  degree_is k (assoc k p q) (assoc_degree p q).
Proof.
  revert p q. induction k as [|n IH]; intros p q Hk Hp Hq Hp0 Hq0 Hpq; [lia|].
  pose proof (Nat.pow_nonzero 2 n ltac:(lia)) as Hh.
  assert (forall a b, a < Nat.pow 2 n -> b < Nat.pow 2 n -> deg_le n (assoc n a b) (n - 2)) as Lower.
  { intros a b Ha Hb.
    destruct (Nat.eq_dec a 0) as [Ha0|Ha0]; [apply deg_le_zero; intros; apply assoc_degenerate; auto|].
    destruct (Nat.eq_dec b 0) as [Hb0|Hb0]; [apply deg_le_zero; intros; apply assoc_degenerate; auto|].
    destruct (Nat.eq_dec a b) as [Hab|Hab]; [apply deg_le_zero; intros; apply assoc_degenerate; auto|].
    destruct (Nat.eq_dec n 2) as [->|Hn].
    - apply deg_le_zero. intros x Hx. simpl in Ha, Hb, Hx. apply assoc_quaternion; assumption.
    - apply (deg_le_mono n _ (assoc_degree a b)); [|exact (proj1 (IH a b ltac:(lia) Ha Hb Ha0 Hb0 Hab))].
      pose proof (max_bounds a b (Nat.pow 2 n) ltac:(lia) ltac:(lia) Ha Hb) as M.
      assert (Nat.log2 (Nat.max a b) < n) by (apply Nat.log2_lt_pow2; lia).
      unfold assoc_degree. apply Nat.max_lub; lia. }
  destruct (Nat.ltb_spec p (Nat.pow 2 n)) as [Hpl|Hpl], (Nat.ltb_spec q (Nat.pow 2 n)) as [Hql|Hql].
  - (* p and q in the low half: g = g' + xi. *)
    assert (cst p q = true) as Hc.
    { unfold cst. rewrite lxor_eqb_0, (proj2 (Nat.eqb_neq p 0) Hp0), (proj2 (Nat.eqb_neq q 0) Hq0),
        (proj2 (Nat.eqb_neq p q) Hpq). reflexivity. }
    destruct (Nat.eq_dec n 2) as [->|Hn].
    + simpl in Hpl, Hql.
      replace (assoc_degree p q) with 1.
      2: { pose proof (max_bounds p q 4 ltac:(lia) ltac:(lia) Hpl Hql) as M.
           assert (Nat.log2 (Nat.max p q) < 2) by (apply Nat.log2_lt_pow2; simpl; lia).
           unfold assoc_degree. rewrite Nat.max_l by lia. reflexivity. }
      apply lift_zero; intros y Hy; simpl in Hy.
      * rewrite assoc_low by (simpl; lia). apply assoc_quaternion; assumption.
      * rewrite assoc_high_ll, Hc, assoc_low, assoc_quaternion by (simpl; lia). reflexivity.
    + apply (lift n _ (assoc n p q) true); [apply Nat.le_max_l|apply IH; lia| |].
      * intros y Hy. apply assoc_low; assumption.
      * intros y Hy. rewrite assoc_high_ll, Hc by assumption. reflexivity.
  - (* q reaches the top half. *)
    destruct (split_high n q Hq Hql) as [q' [Hq' ->]].
    assert (assoc_degree p (q' + Nat.pow 2 n) = n - 1) as D.
    { unfold assoc_degree. rewrite (Nat.max_r p (q' + Nat.pow 2 n)) by lia.
      rewrite (Nat.log2_unique _ n) by (simpl in *; lia). apply Nat.max_r. lia. }
    rewrite D. apply (lift n _ (assoc (S n) p (q' + Nat.pow 2 n)) (cst p q')); [lia| |reflexivity|].
    2: { intros y Hy. apply assoc_high_lh; assumption. }
    apply (upper_degree n _ (assoc n p q') q' (Nat.lxor q' p) (xorb (negb (Nat.eqb p 0)) (alt p q')));
      [lia|assumption|apply lxor_lt; assumption| |apply Lower; assumption|].
    + intro E. pose proof (lxor_eqb_self q' p) as S. rewrite <- E, Nat.eqb_refl in S.
      symmetry in S. apply Nat.eqb_eq in S. contradiction.
    + intros y Hy. rewrite assoc_lh_low by assumption.
      rewrite (alt_delta p (Nat.lxor q' y)), !eqb_lxor, Nat.lxor_0_r. btauto.
  - (* p reaches the top half. *)
    destruct (split_high n p Hp Hpl) as [p' [Hp' ->]].
    assert (assoc_degree (p' + Nat.pow 2 n) q = n - 1) as D.
    { unfold assoc_degree. rewrite (Nat.max_l (p' + Nat.pow 2 n) q) by lia.
      rewrite (Nat.log2_unique _ n) by (simpl in *; lia). apply Nat.max_r. lia. }
    rewrite D. apply (lift n _ (assoc (S n) (p' + Nat.pow 2 n) q) (cst p' q)); [lia| |reflexivity|].
    2: { intros y Hy. apply assoc_high_hl; assumption. }
    apply (upper_degree n _ (assoc n p' q) q 0 (negb (Nat.eqb q 0)));
      [lia|assumption|lia|exact Hq0|apply Lower; assumption|].
    intros y Hy. rewrite assoc_hl_low by assumption. rewrite eqb_lxor, Nat.lxor_0_r. btauto.
  - (* p and q both reach the top half. *)
    destruct (split_high n p Hp Hpl) as [p' [Hp' ->]], (split_high n q Hq Hql) as [q' [Hq' ->]].
    assert (assoc_degree (p' + Nat.pow 2 n) (q' + Nat.pow 2 n) = n - 1) as D.
    { unfold assoc_degree. pose proof (max_bounds (p' + Nat.pow 2 n) (q' + Nat.pow 2 n) (Nat.pow 2 (S n))
        ltac:(lia) ltac:(lia) Hp Hq) as M.
      assert (Nat.pow 2 n <= Nat.max (p' + Nat.pow 2 n) (q' + Nat.pow 2 n)) by
        (eapply Nat.le_trans; [|apply Nat.le_max_l]; lia).
      rewrite (Nat.log2_unique _ n) by (simpl in *; lia). apply Nat.max_r. lia. }
    rewrite D.
    apply (lift n _ (assoc (S n) (p' + Nat.pow 2 n) (q' + Nat.pow 2 n)) (cst p' q')); [lia| |reflexivity|].
    2: { intros y Hy. apply assoc_high_hh; assumption. }
    apply (upper_degree n _ (assoc n p' q') (Nat.lxor q' p') 0
      (xorb (negb (Nat.eqb p' 0)) (xorb (alt p' q') (negb (Nat.eqb q' 0)))));
      [lia|apply lxor_lt; assumption|lia| |apply Lower; assumption|].
    + rewrite <- (Nat.eqb_neq _ 0), lxor_eqb_0. apply Nat.eqb_neq. lia.
    + intros y Hy. rewrite assoc_hh_low by assumption.
      rewrite (alt_delta p' (Nat.lxor q' y)), !eqb_lxor, !Nat.lxor_0_r. btauto.
Qed.
