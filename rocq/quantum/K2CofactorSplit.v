(** * Split factored cofactor certificate: step checks, telescoping and basis changes.

    A quadric f = q(G) lies in the local ideal of J ++ m_products n G 2 ([in_local_ideal] of
    HilbertCellCertificate.v, [LI] of K2HilbertBound.v) when a chain of remainders R_0 = f, R_1, .., R_m = []
    satisfies, for each step j, that R_j - R_{j+1} is a combination of the generators with the cofactors of the
    step. [check_step] is the factored check of K2CofactorFactored.v on a polynomial X in place of u f, with the
    unit 1: it forms X - sum_k a_k J_k - sum_a G_a H_a (H_a the Horner sum of the b cofactors, normalized
    modulo p) in a monomial trie and tests every coefficient modulo p. A step reads its cofactors in the sparse
    format of K2CofactorCertificate.v, so a file holds the cofactors of a few J indices and a few Horner
    indices and the polynomials R_j, R_{j+1} as packed words, and its check builds a trie of that file's
    products only. [LI_tele] adds a step to a proved remainder, so the steps of one quadric, each proved in
    its own module, give the quadric. [qscale] and [LI_recover] recover a quadric q1 from a certified
    combination q1 + d q2 and a certified q2, since [subst_q] is linear in the quadric.

    Convention: polynomials, [pcoef], [padd], [pneg], [tri], [norm_poly] and [hlist] are those of
    HilbertCellCertificate.v and K2CofactorFactored.v. A remainder is stored as a list of chunks (k, w); the
    word w holds k terms of b + s n bits each, the coefficient in the low b bits and the exponents of
    t_1 .. t_n above it in s bits each ([dec_polyw]). The cofactor words keep the four-bit exponents of
    [dec_poly] in K2CofactorCertificate.v.

    Main results: [check_step_sound] and [check_step_data_sound] (an accepted step puts X in the local ideal),
    [LI_tele] (a step and a proved remainder prove the previous remainder), [LI_recover] (a certified
    combination and the certified second quadric prove the first), [ksum_subst_q_comb] (linearity of
    [subst_q]), [prime_p32029], and a two-step toy chain over F_7 with known-bad steps ([toy_chain_in_ideal],
    four [_rejected_s] lemmas). *)

From Stdlib Require Import ZArith Lia List Bool PeanoNat NArith Znumtheory.
Require Import HilbertCellCertificate K2CofactorCertificate K2CofactorFactored K2HilbertBound.
Import ListNotations.
Open Scope Z_scope.

(** * The step check *)

Definition check_step (p : Z) (n : nat) (J G : list poly) (u X : poly) (cofs : list poly) : bool :=
  Z.ltb 0 p &&
  negb (Z.eqb (const_coef u mod p) 0) &&
  wf_b n u && forallb (wf_b n) cofs &&
  Nat.eqb (length cofs) (length J + n * tri (length G)) &&
  tall p (hfold (tcombo (-1) (tmul 1 TL u X) (firstn (length J) cofs) J)
    (hlist p n G (map (norm_poly p)
      (stage1 n (seq 0 n) (chunk (tri (length G)) n (skipn (length J) cofs))
        (repeat [] (tri (length G))))))).

Theorem check_step_sound (p : Z) (n : nat) (J G : list poly) (u X : poly) (cofs : list poly) :
  check_step p n J G u X cofs = true ->
  in_local_ideal p n (J ++ m_products n G 2) X.
Proof.
  unfold check_step. intros H.
  repeat (apply andb_true_iff in H as [H ?]).
  match goal with
  | [ Hp : Z.ltb 0 p = true, Hu : negb (Z.eqb (const_coef u mod p) 0) = true,
      Hw : wf_b n u = true, Hc : forallb (wf_b n) cofs = true,
      Hl : Nat.eqb _ _ = true, Ht : tall _ _ = true |- _ ] =>
    assert (Hp0 : p <> 0) by (apply Z.ltb_lt in Hp; lia);
    apply Nat.eqb_eq in Hl;
    exists u, cofs;
    refine (conj (wf_b_sound _ _ Hw) (conj _ (conj _ (conj _ _))));
    [ apply Forall_forall; intros f Hf; rewrite forallb_forall in Hc;
      exact (wf_b_sound _ _ (Hc f Hf))
    | rewrite length_app, m_products_len; exact Hl
    | intros Hcg; apply negb_true_iff in Hu; apply Z.eqb_neq in Hu; apply Hu;
      apply (proj2 (Z.mod_divide _ _ Hp0)); unfold cg in Hcg; rewrite Z.sub_0_r in Hcg; exact Hcg
    | intros m; unfold padd; rewrite pcoef_app, pcoef_pneg;
      pose proof (tall_sound p _ Ht (enc m)) as E;
      rewrite hfold_get, tcombo_get, tmul_get in E;
      apply cg_zero_of_mod in E;
      pose proof (master p Hp0 n J G cofs m Hl) as Hm;
      exact (cg_combine p _ _ _ _ _ eq_refl E Hm) ]
  end.
Qed.


Definition check_step_data (p : Z) (n : nat) (J G : list poly) (X : poly)
  (sp : list (nat * list (nat * N))) : bool :=
  check_step p n J G (one_poly n) X (dense_cofs 16 n (length J + n * tri (length G)) sp).

Theorem check_step_data_sound (p : Z) (n : nat) (J G : list poly) (X : poly)
  (sp : list (nat * list (nat * N))) :
  check_step_data p n J G X sp = true -> LI p n (J ++ m_products n G 2) X.
Proof.
  unfold check_step_data. intros H. apply LI_of_ili. exact (check_step_sound _ _ _ _ _ _ _ H).
Qed.

(** * Remainder words *)

Fixpoint dec_monow (s : N) (n : nat) (w : N) : mono :=
  match n with
  | O => []
  | S n' => N.to_nat (N.land w (N.ones s)) :: dec_monow s n' (N.shiftr w s)
  end.

Fixpoint dec_chunkw (b s : N) (n : nat) (k : nat) (w : N) : poly :=
  match k with
  | O => []
  | S k' =>
    (dec_monow s n (N.shiftr w b), Z.of_N (N.land w (N.ones b)))
      :: dec_chunkw b s n k' (N.shiftr w (b + s * N.of_nat n))
  end.

Definition dec_polyw (b s : N) (n : nat) (chunks : list (nat * N)) : poly :=
  flat_map (fun c => dec_chunkw b s n (fst c) (snd c)) chunks.

(** * Telescoping *)

Lemma LI_tele p n gens R R' :
  prime p -> LI p n gens (padd R (pneg R')) -> LI p n gens R' -> LI p n gens R.
Proof.
  intros Hp H1 H2.
  apply (LI_pe p n gens R (padd R (pneg R') ++ R')); [|exact (LI_add p n gens _ _ Hp H1 H2)].
  intros F. unfold padd, pneg. rewrite !ksum_app, ksum_neg_list. apply cg_eq. ring.
Qed.

(** * Linearity of the substitution in the quadric *)

Definition qscale (c : Z) (q : list (Z * list nat)) : list (Z * list nat) :=
  map (fun t => (c * fst t, snd t)) q.

Lemma subst_q_cons n G t q :
  subst_q n G (t :: q) =
  map (fun x => (fst x, fst t * snd x)) (ymono n G (snd t)) ++ subst_q n G q.
Proof. unfold subst_q. cbn [map lincomb]. reflexivity. Qed.

Lemma ksum_subst_q_app n G q1 q2 F :
  ksum (subst_q n G (q1 ++ q2)) F = ksum (subst_q n G q1) F + ksum (subst_q n G q2) F.
Proof.
  induction q1 as [|t q1 IH].
  - cbn [app]. unfold subst_q at 2. cbn [map lincomb]. rewrite ksum_nil. ring.
  - cbn [app]. rewrite !subst_q_cons, !ksum_app, IH. ring.
Qed.

Lemma ksum_subst_q_scale n G c q F :
  ksum (subst_q n G (qscale c q)) F = c * ksum (subst_q n G q) F.
Proof.
  induction q as [|t q IH].
  - unfold qscale, subst_q. cbn [map lincomb]. rewrite ksum_nil. ring.
  - unfold qscale in *. cbn [map]. rewrite !subst_q_cons, !ksum_app, !ksum_scale_list. cbn [fst snd].
    rewrite IH. ring.
Qed.

Lemma ksum_subst_q_comb n G q1 q2 d F :
  ksum (subst_q n G (q1 ++ qscale d q2)) F = ksum (subst_q n G q1) F + d * ksum (subst_q n G q2) F.
Proof. rewrite ksum_subst_q_app, ksum_subst_q_scale. reflexivity. Qed.

Lemma LI_recover p n J G q1 q2 d :
  prime p ->
  LI p n J (subst_q n G (q1 ++ qscale d q2)) -> LI p n J (subst_q n G q2) ->
  LI p n J (subst_q n G q1).
Proof.
  intros Hp H1 H2.
  apply (LI_pe p n J (subst_q n G q1)
    (subst_q n G (q1 ++ qscale d q2) ++ kb_scale (- d) (subst_q n G q2)));
    [|exact (LI_add p n J _ _ Hp H1 (LI_scalec p n J (- d) _ H2))].
  intros F. rewrite ksum_app, ksum_kb_scale, ksum_subst_q_comb. apply cg_eq. ring.
Qed.

(** * The prime of the K2 cells *)

Lemma split_in_trial (B : nat) (d : Z) :
  2 <= d -> d <= Z.of_nat B -> In d (map Z.of_nat (seq 2 (B - 1))).
Proof.
  intros H1 H2. apply in_map_iff. exists (Z.to_nat d). split.
  - apply Z2Nat.id. lia.
  - apply in_seq. lia.
Qed.

Lemma split_prime_by_trial (n : Z) (B : nat) :
  1 < n -> n <= Z.of_nat B * Z.of_nat B ->
  forallb (fun d => negb (Z.eqb (n mod d) 0)) (map Z.of_nat (seq 2 (B - 1))) = true ->
  Z.prime n.
Proof.
  intros H1 H2 Hf. split; [exact H1|].
  intros m Hm Hdiv. rewrite forallb_forall in Hf.
  assert (Hbad : forall d, 2 <= d -> d <= Z.of_nat B -> Z.divide d n -> False).
  { intros d Hd1 Hd2 Hd. pose proof (Hf d (split_in_trial B d Hd1 Hd2)) as H0.
    apply Bool.negb_true_iff in H0. apply Z.eqb_neq in H0. apply H0.
    apply Z.mod_divide; [lia | exact Hd]. }
  destruct Hdiv as [k Hk].
  destruct (Z_le_gt_dec m (Z.of_nat B)) as [Hle|Hgt].
  - apply (Hbad m); [lia | exact Hle | exists k; exact Hk].
  - assert (Hk2 : 2 <= k) by nia.
    assert (Hkb : k <= Z.of_nat B) by nia.
    apply (Hbad k Hk2 Hkb). exists m. lia.
Qed.

Lemma prime_p32029 : prime 32029.
Proof.
  apply prime_alt.
  apply (split_prime_by_trial 32029 179);
    [lia | first [lia | (vm_compute; intros H; discriminate H)] | vm_compute; reflexivity].
Qed.

Lemma prime_p7 : prime 7.
Proof.
  apply prime_alt.
  apply (split_prime_by_trial 7 3);
    [lia | first [lia | (vm_compute; intros H; discriminate H)] | vm_compute; reflexivity].
Qed.

(** * A two-step chain over F_7

    The one-variable cell of K2CofactorCertificate.v with the quadric y^2 + y^3: the first step takes
    t^2 = J_0 with the cofactor 1, the second takes t^3 = t G G with the cofactor 1. *)

Definition toy2_q : list (Z * list nat) := [ (1, [2%nat]); (1, [3%nat]) ].
Definition toy2_R0 : poly := subst_q 1 toy_G toy2_q.
Definition toy2_R1 : poly := dec_polyw 16 4 1 [ (1%nat, 0x30001%N) ].
Definition toy2_R2 : poly := [].
Definition toy2_sp1 : list (nat * list (nat * N)) := [ (0%nat, [ (1%nat, 1%N) ]) ].
Definition toy2_sp2 : list (nat * list (nat * N)) := [ (1%nat, [ (1%nat, 1%N) ]) ].

Lemma toy_step1_accepted :
  check_step_data 7 1 toy_J toy_G (padd toy2_R0 (pneg toy2_R1)) toy2_sp1 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_step2_accepted :
  check_step_data 7 1 toy_J toy_G (padd toy2_R1 (pneg toy2_R2)) toy2_sp2 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_remainder_rejected_s :
  check_step_data 7 1 toy_J toy_G
    (padd toy2_R0 (pneg (dec_polyw 16 4 1 [ (1%nat, 0x30002%N) ]))) toy2_sp1 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_remainder_exponent_rejected_s :
  check_step_data 7 1 toy_J toy_G
    (padd toy2_R0 (pneg (dec_polyw 16 4 1 [ (1%nat, 0x20001%N) ]))) toy2_sp1 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_cofactor_rejected_s :
  check_step_data 7 1 toy_J toy_G (padd toy2_R1 (pneg toy2_R2))
    [ (1%nat, [ (1%nat, 2%N) ]) ] = false.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_cofactor_exponent_rejected_s :
  check_step_data 7 1 toy_J toy_G (padd toy2_R0 (pneg toy2_R1))
    [ (0%nat, [ (1%nat, 0x10001%N) ]) ] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem toy_chain_in_ideal :
  in_local_ideal 7 1 (toy_J ++ m_products 1 toy_G 2) (subst_q 1 toy_G toy2_q).
Proof.
  apply ili_of_LI.
  apply (LI_tele 7 1 _ toy2_R0 toy2_R1 prime_p7
    (check_step_data_sound _ _ _ _ _ _ toy_step1_accepted)).
  apply (LI_tele 7 1 _ toy2_R1 toy2_R2 prime_p7
    (check_step_data_sound _ _ _ _ _ _ toy_step2_accepted)).
  apply LI_nil. exact prime_p7.
Qed.

Print Assumptions toy_chain_in_ideal.
Print Assumptions LI_recover.
Print Assumptions check_step_data_sound.
Print Assumptions prime_p32029.
