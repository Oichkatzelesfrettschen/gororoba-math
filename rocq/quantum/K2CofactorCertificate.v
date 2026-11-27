(** Cofactor certificates: a polynomial in the local ideal J + m (G)^d over F_p, checked through a monomial trie.

    A certificate shows that the polynomial f = q(G), the substitution of the generators G_a for the
    variables y_a in a polynomial q of y, lies in the local ideal of the generators J ++ m_products n G d
    (the ideal of J plus t_k times each degree-d product of G), in the sense of [in_local_ideal] of
    HilbertCellCertificate.v: a unit u and a cofactor list cofs, one polynomial per generator, with
    u f - sum_j cofs_j gens_j congruent to 0 modulo p in every coefficient. The checker [check_cofactor]
    adds every monomial product of u f and of the cofactor terms into one trie keyed by an injective
    positive-number code of the monomial and tests that every coefficient sum vanishes modulo p, so
    no product polynomial is normalized and a coefficient lookup costs the length of the key.

    Convention: a polynomial is the list of (monomial, coefficient) pairs of HilbertCellCertificate.v,
    repeated monomials allowed; [pcoef f m] sums the coefficients of the monomial m. A polynomial q of the
    variables y is a list of pairs (coefficient, exponent list of the y_a) and [subst_q n G q] is the
    sum of coefficient times the product of the powers G_a^e_a. The code [enc] writes each exponent e of a
    monomial as e ones and a zero from the low bit up, ended by the leading one; it is injective on all
    exponent lists, so a trie lookup at [enc m] returns the exact sum of the coefficients of m.
    [check_cofactor] holds no hypothesis on p except that p is nonzero and the constant term of u is nonzero
    modulo p; primality enters nowhere because no coefficient is divided. [ymono] truncates at the shorter of G
    and the exponent list, and [check_cofactor] checks no length of an exponent list or of G, so the theorem
    is about [subst_q] of that truncating encoding; see the comment of [ymono].

    Certificate data: a cofactor certificate is read from lists of natural numbers, one number per term:
    the coefficient in the low b bits and above it the exponents of the n variables in four bits each,
    the first variable lowest. A chunk (k, w) packs k consecutive terms into the number w, the first term
    lowest, in slots of b + 4 n bits; a polynomial is a list of chunks, which keeps the number of literals
    small; the cofactors are a sparse list of (generator index, polynomial). The reader is plumbing: the
    soundness theorem holds for every certificate it could return.

    Main results: [check_cofactor_sound] (an accepted certificate puts subst_q n G q in the local ideal of
    J ++ m_products n G d, for every integer p); [check_data_sound] (the same for certificate data);
    [toy_accepted] and four [_rejected] lemmas (a one-variable cell over F_7 with a unit u = 1 + t, and
    single-entry mutants of a coefficient, an exponent, the constant term of u and the cofactor count);
    [toy_data_accepted] and [toy_data_rejected] (the same cell through the data reader). *)

From Stdlib Require Import ZArith Lia List Bool PeanoNat NArith.
Require Import HilbertCellCertificate.
Import ListNotations.
Open Scope Z_scope.

(** * An injective code of monomials *)

Fixpoint push_nat (e : nat) (k : positive) : positive :=
  match e with
  | O => xO k
  | S e' => xI (push_nat e' k)
  end.

Fixpoint enc (m : mono) : positive :=
  match m with
  | [] => xH
  | e :: m' => push_nat e (enc m')
  end.

Lemma push_nat_inj e : forall e' k k', push_nat e k = push_nat e' k' -> e = e' /\ k = k'.
Proof.
  induction e as [|e IH]; intros e' k k' H; destruct e' as [|e']; simpl in H; try discriminate H.
  - injection H as ->. split; reflexivity.
  - injection H as H1. destruct (IH _ _ _ H1) as [-> ->]. split; reflexivity.
Qed.

Lemma enc_inj a : forall b, enc a = enc b -> a = b.
Proof.
  induction a as [|e a IH]; intros [|e' b] H; simpl in H.
  - reflexivity.
  - destruct e'; simpl in H; discriminate H.
  - destruct e; simpl in H; discriminate H.
  - destruct (push_nat_inj _ _ _ _ H) as [-> H1]. rewrite (IH _ H1). reflexivity.
Qed.

(** * A trie of integers indexed by positive numbers *)

Inductive tr : Set :=
  | TL : tr
  | TN : tr -> Z -> tr -> tr.

Fixpoint tget (t : tr) (k : positive) : Z :=
  match t with
  | TL => 0
  | TN l v r => match k with xH => v | xO k' => tget l k' | xI k' => tget r k' end
  end.

Fixpoint tadd (t : tr) (k : positive) (c : Z) : tr :=
  match k with
  | xH => match t with TL => TN TL c TL | TN l v r => TN l (v + c) r end
  | xO k' => match t with TL => TN (tadd TL k' c) 0 TL | TN l v r => TN (tadd l k' c) v r end
  | xI k' => match t with TL => TN TL 0 (tadd TL k' c) | TN l v r => TN l v (tadd r k' c) end
  end.

Lemma tget_tadd k : forall t c k',
  tget (tadd t k c) k' = tget t k' + (if Pos.eqb k k' then c else 0).
Proof.
  induction k as [k IH|k IH|]; intros t c k'; destruct t as [|l v r]; destruct k' as [k'|k'|];
    simpl; try rewrite IH; simpl; try (destruct (Pos.eqb k k')); lia.
Qed.

Fixpoint tall (p : Z) (t : tr) : bool :=
  match t with
  | TL => true
  | TN l v r => Z.eqb (v mod p) 0 && tall p l && tall p r
  end.

Lemma tall_sound p : forall t, tall p t = true -> forall k, tget t k mod p = 0.
Proof.
  induction t as [|l IHl v r IHr]; intros H k; [reflexivity|].
  simpl in H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  destruct k as [k|k|]; simpl; [apply IHr; exact H3 | apply IHl; exact H2 | apply Z.eqb_eq; exact H1].
Qed.

Lemma pcoef_nil m : pcoef [] m = 0.
Proof. reflexivity. Qed.

Lemma pcoef_cons x l m :
  pcoef (x :: l) m = (if mono_eq_dec (fst x) m then snd x else 0) + pcoef l m.
Proof. reflexivity. Qed.

Lemma pcoef_app f g m : pcoef (f ++ g) m = pcoef f m + pcoef g m.
Proof. unfold pcoef. apply kcoef_app. Qed.

Lemma pcoef_pneg f m : pcoef (pneg f) m = - pcoef f m.
Proof.
  induction f as [|x f IH]; [reflexivity|].
  unfold pneg in *. simpl map. rewrite !pcoef_cons, IH. cbn [fst snd].
  destruct (mono_eq_dec (fst x) m); ring.
Qed.

Lemma tadd_enc t x c m :
  tget (tadd t (enc x) c) (enc m) = tget t (enc m) + (if mono_eq_dec x m then c else 0).
Proof.
  rewrite tget_tadd. destruct (mono_eq_dec x m) as [->|N].
  - rewrite Pos.eqb_refl. reflexivity.
  - assert (Pos.eqb (enc x) (enc m) = false) as ->.
    { destruct (Pos.eqb (enc x) (enc m)) eqn:E; [|reflexivity].
      apply Pos.eqb_eq in E. apply enc_inj in E. contradiction. }
    reflexivity.
Qed.

(** * Accumulating products and combinations into the trie *)

Definition tstep (s : Z) (a : mono * Z) (t : tr) (b : mono * Z) : tr :=
  tadd t (enc (madd (fst a) (fst b))) (s * (snd a * snd b)).

Definition trow (s : Z) (a : mono * Z) (g : poly) (t : tr) : tr := fold_left (tstep s a) g t.

Definition tmul (s : Z) (t : tr) (f g : poly) : tr := fold_left (fun t a => trow s a g t) f t.

Fixpoint tcombo (s : Z) (t : tr) (cs gs : list poly) : tr :=
  match cs, gs with
  | c :: cs', g :: gs' => tcombo s (tmul s t c g) cs' gs'
  | _, _ => t
  end.

Lemma trow_get s a g m : forall t,
  tget (trow s a g t) (enc m) = tget t (enc m)
    + s * pcoef (map (fun b => (madd (fst a) (fst b), snd a * snd b)) g) m.
Proof.
  induction g as [|b g IH]; intros t; unfold trow in *; simpl fold_left.
  - simpl map. rewrite pcoef_nil. ring.
  - rewrite IH. unfold tstep. rewrite tadd_enc. simpl map. rewrite pcoef_cons. simpl fst.
    destruct (mono_eq_dec (madd (fst a) (fst b)) m); simpl; ring.
Qed.

Lemma tmul_get s g m : forall f t,
  tget (tmul s t f g) (enc m) = tget t (enc m) + s * pcoef (pmul f g) m.
Proof.
  induction f as [|a f IH]; intros t; unfold tmul in *; simpl fold_left.
  - unfold pmul. simpl flat_map. rewrite pcoef_nil. ring.
  - rewrite IH, trow_get.
    change (pmul (a :: f) g) with (map (fun b => (madd (fst a) (fst b), snd a * snd b)) g ++ pmul f g).
    rewrite pcoef_app. ring.
Qed.

Lemma tcombo_get s m : forall cs gs t,
  tget (tcombo s t cs gs) (enc m) = tget t (enc m) + s * pcoef (combo cs gs) m.
Proof.
  induction cs as [|c cs IH]; intros gs t; destruct gs as [|g gs]; simpl tcombo; simpl combo;
    try (rewrite pcoef_nil; ring).
  rewrite IH, tmul_get, pcoef_app. ring.
Qed.

Lemma tree_pzero p u f cofs gens :
  tall p (tcombo (-1) (tmul 1 TL u f) cofs gens) = true ->
  pzero p (padd (pmul u f) (pneg (combo cofs gens))).
Proof.
  intros H m. apply cg_zero_of_mod.
  pose proof (tall_sound p _ H (enc m)) as E.
  rewrite tcombo_get, tmul_get in E.
  unfold padd. rewrite pcoef_app, pcoef_pneg.
  replace (tget TL (enc m)) with 0 in E by reflexivity.
  replace (pcoef (pmul u f) m + - pcoef (combo cofs gens) m)
    with (0 + (0 + 1 * pcoef (pmul u f) m) + -1 * pcoef (combo cofs gens) m) by ring.
  exact E.
Qed.

(** * Substitution of the generators into a polynomial of y *)

Fixpoint pow_poly (n : nat) (g : poly) (k : nat) : poly :=
  match k with
  | O => one_poly n
  | S k' => pmul g (pow_poly n g k')
  end.

(** [ymono n G e] stops at the end of G or of e: a term whose exponent list is shorter than G drops the
    trailing generators (a missing exponent acts as zero) and a term whose list is longer drops the trailing
    exponents. [check_cofactor] checks neither the length of the exponent lists of q, nor [length G] against
    them, nor the well-formedness of J and G; it checks the unit, the cofactors and the trie. Its soundness
    theorem therefore concerns [subst_q] of this truncating encoding, and two lists q that differ only in
    exponents beyond [length G] give one [subst_q]. Reading q as an ordinary polynomial in y_1 .. y_k needs the
    extra hypotheses that every exponent list of q has length [length G] and that G is [wf_poly n]; the
    [check_red] of K2HilbertBound.v checks both. *)
Fixpoint ymono (n : nat) (G : list poly) (e : list nat) : poly :=
  match G, e with
  | g :: G', k :: e' => pmul (pow_poly n g k) (ymono n G' e')
  | _, _ => one_poly n
  end.

Definition subst_q (n : nat) (G : list poly) (q : list (Z * list nat)) : poly :=
  lincomb (map fst q) (map (fun t => ymono n G (snd t)) q).

(** * The checker and its soundness *)

Record kcert := mk_kcert { k_u : poly; k_cofs : list poly }.

Definition wf_b (n : nat) (f : poly) : bool := forallb (fun t => Nat.eqb (length (fst t)) n) f.

Lemma wf_b_sound n f : wf_b n f = true -> wf_poly n f.
Proof.
  unfold wf_b, wf_poly. intros H. apply Forall_forall. intros t Ht.
  rewrite forallb_forall in H. apply Nat.eqb_eq. exact (H t Ht).
Qed.

Definition check_cofactor (p : Z) (n : nat) (J G : list poly) (d : nat) (q : list (Z * list nat))
  (c : kcert) : bool :=
  let gens := J ++ m_products n G d in
  negb (Z.eqb p 0) && negb (Z.eqb (const_coef (k_u c) mod p) 0) &&
  wf_b n (k_u c) && forallb (wf_b n) (k_cofs c) &&
  Nat.eqb (length (k_cofs c)) (length gens) &&
  tall p (tcombo (-1) (tmul 1 TL (k_u c) (subst_q n G q)) (k_cofs c) gens).

Theorem check_cofactor_sound p n J G d q c :
  check_cofactor p n J G d q c = true ->
  in_local_ideal p n (J ++ m_products n G d) (subst_q n G q).
Proof.
  unfold check_cofactor. intros H.
  repeat (apply andb_true_iff in H as [H ?]).
  match goal with
  | [ Hp : negb (Z.eqb p 0) = true, Hu : negb (Z.eqb (const_coef (k_u c) mod p) 0) = true,
      Hw : wf_b n (k_u c) = true, Hc : forallb (wf_b n) (k_cofs c) = true,
      Hl : Nat.eqb _ _ = true, Ht : tall _ _ = true |- _ ] =>
    exists (k_u c), (k_cofs c);
    refine (conj (wf_b_sound _ _ Hw) (conj _ (conj (proj1 (Nat.eqb_eq _ _) Hl) (conj _ _))));
    [ apply Forall_forall; intros f Hf; rewrite forallb_forall in Hc;
      exact (wf_b_sound _ _ (Hc f Hf))
    | intros Hcg; apply negb_true_iff in Hu; apply Z.eqb_neq in Hu; apply Hu;
      apply negb_true_iff in Hp; apply Z.eqb_neq in Hp;
      apply (proj2 (Z.mod_divide _ _ Hp)); unfold cg in Hcg; rewrite Z.sub_0_r in Hcg; exact Hcg
    | exact (tree_pzero _ _ _ _ _ Ht) ]
  end.
Qed.

(** * The certificate data reader *)

Record kdata := mk_kdata { kd_u : list (nat * N); kd_cofs : list (nat * list (nat * N)) }.

Fixpoint dec_mono (n : nat) (w : N) : mono :=
  match n with
  | O => []
  | S n' => N.to_nat (N.land w 15) :: dec_mono n' (N.shiftr w 4)
  end.

Fixpoint dec_chunk (b : N) (n : nat) (k : nat) (w : N) : poly :=
  match k with
  | O => []
  | S k' =>
    (dec_mono n (N.shiftr w b), Z.of_N (N.land w (N.ones b)))
      :: dec_chunk b n k' (N.shiftr w (b + 4 * N.of_nat n))
  end.

Definition dec_poly (b : N) (n : nat) (chunks : list (nat * N)) : poly :=
  flat_map (fun c => dec_chunk b n (fst c) (snd c)) chunks.

Definition dense_cofs (b : N) (n ng : nat) (sp : list (nat * list (nat * N))) : list poly :=
  map (fun j => flat_map (fun e => if Nat.eqb (fst e) j then dec_poly b n (snd e) else []) sp)
    (seq 0 ng).

Definition decode_cert (b : N) (n ng : nat) (d : kdata) : kcert :=
  mk_kcert (dec_poly b n (kd_u d)) (dense_cofs b n ng (kd_cofs d)).

Definition check_data (p : Z) (n : nat) (J G : list poly) (d : nat) (q : list (Z * list nat))
  (b : N) (dat : kdata) : bool :=
  check_cofactor p n J G d q (decode_cert b n (length (J ++ m_products n G d)) dat).

Theorem check_data_sound p n J G d q b dat :
  check_data p n J G d q b dat = true -> in_local_ideal p n (J ++ m_products n G d) (subst_q n G q).
Proof. unfold check_data. apply check_cofactor_sound. Qed.

(** * A one-variable cell over F_7 *)

Definition toy_J : list poly := [ [([2%nat], 1)] ].
Definition toy_G : list poly := [ [([1%nat], 1)] ].
Definition toy_q : list (Z * list nat) := [ (1, [2%nat]) ].

Definition toy_cert : kcert :=
  mk_kcert [([0%nat], 1); ([1%nat], 1)] [ [([0%nat], 1)]; [([0%nat], 1)] ].

Lemma toy_accepted : check_cofactor 7 1 toy_J toy_G 2 toy_q toy_cert = true.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_coefficient_rejected :
  check_cofactor 7 1 toy_J toy_G 2 toy_q
    (mk_kcert [([0%nat], 1); ([1%nat], 1)] [ [([0%nat], 1)]; [([0%nat], 2)] ]) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_exponent_rejected :
  check_cofactor 7 1 toy_J toy_G 2 toy_q
    (mk_kcert [([0%nat], 1); ([1%nat], 1)] [ [([0%nat], 1)]; [([1%nat], 1)] ]) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_unit_rejected :
  check_cofactor 7 1 toy_J toy_G 2 toy_q
    (mk_kcert [([1%nat], 1)] [ [([0%nat], 1)]; [([0%nat], 1)] ]) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_count_rejected :
  check_cofactor 7 1 toy_J toy_G 2 toy_q
    (mk_kcert [([0%nat], 1); ([1%nat], 1)] [ [([0%nat], 1)] ]) = false.
Proof. vm_compute. reflexivity. Qed.

Definition toy_data (c : N) : kdata :=
  mk_kdata [ (2%nat, 0x400080001%N) ] [ (0%nat, [ (1%nat, 1%N) ]); (1%nat, [ (1%nat, c) ]) ].

Lemma toy_data_accepted : check_data 7 1 toy_J toy_G 2 toy_q 15 (toy_data 1) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_data_rejected : check_data 7 1 toy_J toy_G 2 toy_q 15 (toy_data 2) = false.
Proof. vm_compute. reflexivity. Qed.

Theorem toy_in_ideal :
  in_local_ideal 7 1 (toy_J ++ m_products 1 toy_G 2) (subst_q 1 toy_G toy_q).
Proof. exact (check_cofactor_sound _ _ _ _ _ _ _ toy_accepted). Qed.

Print Assumptions toy_in_ideal.
Print Assumptions check_data_sound.
Print Assumptions toy_data_accepted.
