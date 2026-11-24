(** Module certificates for the Hilbert-function cells of a local ring over a prime field.

    A cell fixes a prime p, a number n of variables, a list J of polynomials in n variables (the ideal of the
    ambient variety), a list G of polynomials (the generators of the ideal whose fiber cone is measured) and
    a degree d. The local ring is R = F_p[t_1 .. t_n]_(t) / (J), P_d is the span of the degree-d products of
    the entries of G, and the cell claims that the quotient (P_d + J) / (m P_d + J) of R has a basis of r
    products, where m = (t_1 .. t_n). This file states the claim ([hilbert_cell]) and proves a checkable
    sufficient condition for its independence half ([check_cert], [cert_independent]).

    Convention: [cg p a b] means p divides a - b, so every statement reads modulo p and no hypothesis on p
    enters until the final cancellation of a nonzero constant term, which uses [prime p]. A vector is a list
    of integers; an entry past the end of the list reads as 0 and two vectors are equal ([veq]) when every
    entry is congruent. A sparse matrix is a list of rows, row b a list of pairs (key k, value v) with
    repeated keys allowed, where the positive key k names column k - 1 ([ridx]); it sends x to the vector whose
    entry b is the sum of v x_(k-1) over row b, reduced modulo p ([mv]). [mv] reads x through a binary trie
    keyed by positive numbers ([vtree]), so one read costs O(log q) in the length q of x. A monomial is an exponent vector of length n and a polynomial a list of pairs
    (monomial, coefficient) with repeated monomials allowed; [pcoef] sums the coefficients of one monomial and
    [pzero p f] says every such sum is congruent to 0. A monomial acts on a vector through the list [ops] of
    n operators by iterating operator k exactly e_k times ([mono_apply]); [ev] adds the coefficient
    multiples. The products of G of degree d ([products]) list the multisets of generators in the order of
    [msets]: the first generator g times the products of degree d - 1 of the same generator list, then the
    products of the tail of G; [m_products] lists t_k times each product, k below n. A polynomial f lies in
    the local ideal of the gens ([in_local_ideal]) when u f - sum of cofs_j gens_j is [pzero], with
    the cofactors of exponent length n and the coefficient of the zero monomial of u nonzero modulo p.

    A certificate ([cert]) holds n commuting sparse operators on F_p^q, a level list on the q basis
    vectors, a vector e, a sparse left-inverse matrix and the indices of the selected products. [check_cert]
    tests, by computation: (a) the operators commute (the rows of M N and N M agree after merging columns);
    (b) every nonzero entry of every operator goes from a lower level to a higher one; (c) every generator
    of J sends e to 0; (d) every operator sends the vector of every product to 0, the vector of a product
    being computed along the order of [msets]; (e) the left-inverse sends the vector of the i-th selected
    product to the i-th unit vector.

    Main results: [cert_independent] (a certificate accepted by [check_cert] makes the selected products
    independent modulo the local ideal (J, m P_d) for prime p); [check_cert_sel_range] (the selected indices
    lie in [products]); [toy_cert_accepted] and the six [_rejected] lemmas (a two-variable cell over F_7 and
    six single-entry mutants, by vm_compute); [toy_independent] (the first instantiated). The spanning half of
    [hilbert_cell] ([spans_mod]) is stated and not certified here. *)

From Stdlib Require Import ZArith Lia List Znumtheory Setoid Morphisms Bool PeanoNat.
Import ListNotations.
Open Scope Z_scope.

(** * Congruence modulo p *)

Definition cg (p a b : Z) : Prop := Z.divide p (a - b).

Lemma cg_refl p a : cg p a a.
Proof. unfold cg. rewrite Z.sub_diag. apply Z.divide_0_r. Qed.

Lemma cg_sym p a b : cg p a b -> cg p b a.
Proof.
  unfold cg. intros H.
  replace (b - a) with (- (a - b)) by ring.
  exact (proj2 (Z.divide_opp_r p (a - b)) H).
Qed.

Lemma cg_trans p a b c : cg p a b -> cg p b c -> cg p a c.
Proof.
  unfold cg. intros H1 H2.
  replace (a - c) with ((a - b) + (b - c)) by ring.
  exact (Z.divide_add_r _ _ _ H1 H2).
Qed.

Lemma cg_eq p a b : a = b -> cg p a b.
Proof. intros ->. apply cg_refl. Qed.

Lemma cg_add p a a' b b' : cg p a a' -> cg p b b' -> cg p (a + b) (a' + b').
Proof.
  unfold cg. intros H1 H2.
  replace (a + b - (a' + b')) with ((a - a') + (b - b')) by ring.
  exact (Z.divide_add_r _ _ _ H1 H2).
Qed.

Lemma cg_mul p a a' b b' : cg p a a' -> cg p b b' -> cg p (a * b) (a' * b').
Proof.
  unfold cg. intros H1 H2.
  replace (a * b - a' * b') with (a * (b - b') + (a - a') * b') by ring.
  apply Z.divide_add_r.
  - exact (Z.divide_mul_r _ _ _ H2).
  - exact (Z.divide_mul_l _ _ _ H1).
Qed.

Lemma cg_opp p a a' : cg p a a' -> cg p (- a) (- a').
Proof.
  unfold cg. intros H.
  replace (- a - - a') with (- (a - a')) by ring.
  exact (proj2 (Z.divide_opp_r p (a - a')) H).
Qed.

Lemma cg_sub p a a' b b' : cg p a a' -> cg p b b' -> cg p (a - b) (a' - b').
Proof.
  intros H1 H2.
  replace (a - b) with (a + - b) by ring.
  replace (a' - b') with (a' + - b') by ring.
  apply cg_add; [exact H1 | apply cg_opp; exact H2].
Qed.

Lemma cg_mod p a : cg p (a mod p) a.
Proof.
  unfold cg. pose proof (Z_div_mod_eq_full a p) as H.
  exists (- (a / p)). nia.
Qed.

Lemma cg_mod_cong p a b : cg p a b -> cg p (a mod p) (b mod p).
Proof.
  intros H.
  eapply cg_trans; [apply cg_mod|].
  eapply cg_trans; [exact H|].
  apply cg_sym. apply cg_mod.
Qed.

Lemma cg_zero_of_mod p a : a mod p = 0 -> cg p a 0.
Proof.
  intros H0. unfold cg. pose proof (Z_div_mod_eq_full a p) as H.
  exists (a / p). nia.
Qed.

Lemma cg_zero_add p a b : cg p a 0 -> cg p b 0 -> cg p (a + b) 0.
Proof. unfold cg. rewrite !Z.sub_0_r. apply Z.divide_add_r. Qed.

Lemma cg_zero_mul_l p a b : cg p a 0 -> cg p (a * b) 0.
Proof. unfold cg. rewrite !Z.sub_0_r. intros H. exact (Z.divide_mul_l _ _ _ H). Qed.

Lemma cg_zero_mul_r p a b : cg p b 0 -> cg p (a * b) 0.
Proof. unfold cg. rewrite !Z.sub_0_r. intros H. exact (Z.divide_mul_r _ _ _ H). Qed.

#[export] Instance cg_Equiv (p : Z) : Equivalence (cg p).
Proof. constructor; [exact (cg_refl p) | exact (cg_sym p) | exact (cg_trans p)]. Qed.

#[export] Instance cg_add_Proper (p : Z) : Proper (cg p ==> cg p ==> cg p) Z.add.
Proof. intros a a' Ha b b' Hb. apply cg_add; assumption. Qed.

#[export] Instance cg_mul_Proper (p : Z) : Proper (cg p ==> cg p ==> cg p) Z.mul.
Proof. intros a a' Ha b b' Hb. apply cg_mul; assumption. Qed.

#[export] Instance cg_opp_Proper (p : Z) : Proper (cg p ==> cg p) Z.opp.
Proof. intros a a' Ha. apply cg_opp; assumption. Qed.

#[export] Instance cg_sub_Proper (p : Z) : Proper (cg p ==> cg p ==> cg p) Z.sub.
Proof. intros a a' Ha b b' Hb. apply cg_sub; assumption. Qed.

(** * Keyed sums *)

Section Keyed.
Context {K : Type}.
Variable Keq : forall a b : K, {a = b} + {a <> b}.

Fixpoint ksum (l : list (K * Z)) (F : K -> Z) : Z :=
  match l with
  | [] => 0
  | t :: l' => snd t * F (fst t) + ksum l' F
  end.

Fixpoint kcoef (l : list (K * Z)) (k : K) : Z :=
  match l with
  | [] => 0
  | t :: l' => (if Keq (fst t) k then snd t else 0) + kcoef l' k
  end.

Fixpoint gsumk (ks : list K) (l : list (K * Z)) (F : K -> Z) : Z :=
  match ks with
  | [] => 0
  | k :: ks' => kcoef l k * F k + gsumk ks' l F
  end.

Lemma ksum_app (l1 l2 : list (K * Z)) F : ksum (l1 ++ l2) F = ksum l1 F + ksum l2 F.
Proof. induction l1 as [|t l1 IH]; simpl; [reflexivity | rewrite IH; ring]. Qed.

Lemma ksum_cg p (l : list (K * Z)) (F G : K -> Z) :
  (forall k, cg p (F k) (G k)) -> cg p (ksum l F) (ksum l G).
Proof.
  intros H. induction l as [|t l IH]; simpl; [apply cg_refl|].
  apply cg_add; [apply cg_mul; [apply cg_refl | apply H] | exact IH].
Qed.

Lemma ksum_add_fun (l : list (K * Z)) F G :
  ksum l (fun k => F k + G k) = ksum l F + ksum l G.
Proof. induction l as [|t l IH]; simpl; [reflexivity | rewrite IH; ring]. Qed.

Lemma ksum_scale_fun (l : list (K * Z)) c F :
  ksum l (fun k => c * F k) = c * ksum l F.
Proof. induction l as [|t l IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma ksum_scale_list (l : list (K * Z)) a F :
  ksum (map (fun t => (fst t, a * snd t)) l) F = a * ksum l F.
Proof. induction l as [|t l IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma ksum_neg_list (l : list (K * Z)) F :
  ksum (map (fun t => (fst t, - snd t)) l) F = - ksum l F.
Proof. induction l as [|t l IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma ksum_zero_terms p (l : list (K * Z)) F :
  (forall t, In t l -> cg p (snd t * F (fst t)) 0) -> cg p (ksum l F) 0.
Proof.
  intros H. induction l as [|t l IH]; simpl; [apply cg_refl|].
  apply cg_zero_add.
  - apply H. left. reflexivity.
  - apply IH. intros t' Ht'. apply H. right. exact Ht'.
Qed.

Lemma kcoef_app (l1 l2 : list (K * Z)) k : kcoef (l1 ++ l2) k = kcoef l1 k + kcoef l2 k.
Proof. induction l1 as [|t l1 IH]; simpl; [reflexivity | rewrite IH; ring]. Qed.

Lemma gsumk_app ks (l1 l2 : list (K * Z)) F :
  gsumk ks (l1 ++ l2) F = gsumk ks l1 F + gsumk ks l2 F.
Proof. induction ks as [|k ks IH]; simpl; [reflexivity | rewrite kcoef_app, IH; ring]. Qed.

Lemma gsumk_nil ks F : gsumk ks [] F = 0.
Proof. induction ks as [|k ks IH]; simpl; [reflexivity | rewrite IH; ring]. Qed.

Lemma gsumk_single_notin c k0 F ks : ~ In k0 ks -> gsumk ks [(k0, c)] F = 0.
Proof.
  induction ks as [|k ks IH]; intros H; simpl; [reflexivity|].
  destruct (Keq k0 k) as [E|NE].
  - exfalso. apply H. left. symmetry. exact E.
  - rewrite IH by (intros HI; apply H; right; exact HI). ring.
Qed.

Lemma gsumk_single c k0 F ks : NoDup ks -> In k0 ks -> gsumk ks [(k0, c)] F = c * F k0.
Proof.
  induction ks as [|k ks IH]; intros Hnd Hin; [destruct Hin|].
  apply NoDup_cons_iff in Hnd as [Hni Hnd'].
  simpl. destruct (Keq k0 k) as [E|NE].
  - subst k. rewrite (gsumk_single_notin c k0 F ks Hni). ring.
  - destruct Hin as [E2|Hin'].
    + exfalso. apply NE. symmetry. exact E2.
    + rewrite (IH Hnd' Hin'). ring.
Qed.

Lemma ksum_group (l : list (K * Z)) ks F :
  NoDup ks -> (forall t, In t l -> In (fst t) ks) -> ksum l F = gsumk ks l F.
Proof.
  intros Hnd. induction l as [|t l IH]; intros Hin.
  - rewrite gsumk_nil. reflexivity.
  - destruct t as [k0 c].
    change ((k0, c) :: l) with ([(k0, c)] ++ l).
    rewrite gsumk_app, ksum_app.
    rewrite (gsumk_single c k0 F ks Hnd (Hin (k0, c) (or_introl eq_refl))).
    rewrite (IH (fun t' Ht' => Hin t' (or_intror Ht'))).
    simpl. ring.
Qed.

Lemma gsumk_zero p ks (l : list (K * Z)) F :
  (forall k, In k ks -> cg p (kcoef l k) 0) -> cg p (gsumk ks l F) 0.
Proof.
  intros H. induction ks as [|k ks IH]; simpl; [apply cg_refl|].
  apply cg_zero_add.
  - apply cg_zero_mul_l. apply H. left. reflexivity.
  - apply IH. intros k' Hk'. apply H. right. exact Hk'.
Qed.

Lemma ksum_zero_keys p (l : list (K * Z)) F :
  (forall k, In k (map fst l) -> cg p (kcoef l k) 0) -> cg p (ksum l F) 0.
Proof.
  intros H.
  rewrite (ksum_group l (nodup Keq (map fst l)) F (NoDup_nodup Keq (map fst l))).
  - apply gsumk_zero. intros k Hk. apply H.
    exact (proj1 (nodup_In Keq (map fst l) k) Hk).
  - intros t Ht. apply (proj2 (nodup_In Keq (map fst l) (fst t))).
    exact (in_map fst l t Ht).
Qed.

End Keyed.

(** * Vectors and sparse matrices *)

Definition vec := list Z.
Definition row := list (positive * Z).
Definition spmat := list row.

Fixpoint vadd (p : Z) (x y : vec) : vec :=
  match x, y with
  | [], _ => y
  | _, [] => x
  | a :: x', b :: y' => ((a + b) mod p) :: vadd p x' y'
  end.

Fixpoint vscale (p c : Z) (x : vec) : vec :=
  match x with
  | [] => []
  | a :: x' => ((c * a) mod p) :: vscale p c x'
  end.

Definition ridx (c : positive) : nat := Nat.pred (Pos.to_nat c).

Definition xnth (x : vec) (c : positive) : Z := nth (ridx c) x 0.

(** A trie of integers keyed by positive numbers: the key's binary digits, least significant first after the
    leading 1, choose the left (0) or right (1) child; a missing node reads as 0. *)
Inductive ztrie : Set := TL | TN (l : ztrie) (v : Z) (r : ztrie).

Fixpoint tins (k : positive) (a : Z) (t : ztrie) : ztrie :=
  match k with
  | xH => match t with TL => TN TL a TL | TN l _ r => TN l a r end
  | xO k' => match t with TL => TN (tins k' a TL) 0 TL | TN l v r => TN (tins k' a l) v r end
  | xI k' => match t with TL => TN TL 0 (tins k' a TL) | TN l v r => TN l v (tins k' a r) end
  end.

Fixpoint tget (t : ztrie) (c : positive) : Z :=
  match t with
  | TL => 0
  | TN l v r => match c with xH => v | xO c' => tget l c' | xI c' => tget r c' end
  end.

Fixpoint vtree (x : list Z) (k : positive) (t : ztrie) : ztrie :=
  match x with
  | [] => t
  | a :: x' => vtree x' (Pos.succ k) (tins k a t)
  end.

Definition mvt (p : Z) (M : spmat) (t : ztrie) : vec :=
  map (fun r => ksum r (tget t) mod p) M.

Definition mv (p : Z) (M : spmat) (x : vec) : vec := mvt p M (vtree x 1%positive TL).

Lemma tget_tins k : forall a t c,
  tget (tins k a t) c = if Pos.eqb k c then a else tget t c.
Proof.
  induction k as [k IH|k IH|]; intros a t c;
    destruct t as [|l v r]; destruct c as [c|c|]; simpl; try reflexivity; apply IH.
Qed.

Lemma tget_add_same t k a : tget (tins k a t) k = a.
Proof. rewrite tget_tins, Pos.eqb_refl. reflexivity. Qed.

Lemma tget_add_other t k c a : k <> c -> tget (tins k a t) c = tget t c.
Proof.
  intros H. rewrite tget_tins. rewrite (proj2 (Pos.eqb_neq k c) H). reflexivity.
Qed.

Lemma tget_vtree_out (x : list Z) : forall (k : positive) (t : ztrie) (c : positive),
  (Pos.to_nat c < Pos.to_nat k \/ Pos.to_nat k + length x <= Pos.to_nat c)%nat ->
  tget (vtree x k t) c = tget t c.
Proof.
  induction x as [|a x IH]; intros k t c H; [reflexivity|].
  simpl vtree. rewrite IH by (rewrite Pos2Nat.inj_succ; simpl in H; lia).
  apply tget_add_other. intro E. subst c. simpl in H. lia.
Qed.

Lemma tget_vtree_in (x : list Z) : forall (k : positive) (t : ztrie) (c : positive),
  (Pos.to_nat k <= Pos.to_nat c)%nat -> (Pos.to_nat c < Pos.to_nat k + length x)%nat ->
  tget (vtree x k t) c = nth (Pos.to_nat c - Pos.to_nat k) x 0.
Proof.
  induction x as [|a x IH]; intros k t c H1 H2; [simpl in H2; lia|].
  simpl vtree. destruct (Pos.eq_dec k c) as [E|NE].
  - subst c.
    rewrite (tget_vtree_out x (Pos.succ k) (tins k a t) k)
      by (left; rewrite Pos2Nat.inj_succ; lia).
    rewrite tget_add_same, Nat.sub_diag. reflexivity.
  - assert (Hne : Pos.to_nat k <> Pos.to_nat c) by (intro E; apply NE; apply Pos2Nat.inj; exact E).
    rewrite IH by (rewrite Pos2Nat.inj_succ; simpl in H2; lia).
    rewrite Pos2Nat.inj_succ.
    replace (Pos.to_nat c - Pos.to_nat k)%nat with (S (Pos.to_nat c - S (Pos.to_nat k))) by lia.
    reflexivity.
Qed.

Lemma tget_xnth x c : tget (vtree x 1%positive TL) c = xnth x c.
Proof.
  unfold xnth, ridx. pose proof (Pos2Nat.is_pos c) as Hpos.
  destruct (Nat.lt_ge_cases (Pos.to_nat c) (1 + length x)) as [H|H].
  - rewrite tget_vtree_in by (rewrite Pos2Nat.inj_1; lia).
    rewrite Pos2Nat.inj_1. f_equal. lia.
  - rewrite tget_vtree_out by (right; rewrite Pos2Nat.inj_1; lia).
    simpl. symmetry. apply nth_overflow. lia.
Qed.

Lemma ksum_ext {K : Type} (l : list (K * Z)) (F G : K -> Z) :
  (forall c, F c = G c) -> ksum l F = ksum l G.
Proof. intros H. induction l as [|t l IH]; simpl; [reflexivity | rewrite IH, H; reflexivity]. Qed.

Definition veq (p : Z) (x y : vec) : Prop := forall b, cg p (nth b x 0) (nth b y 0).

Lemma veq_refl p x : veq p x x.
Proof. intros b. apply cg_refl. Qed.

Lemma veq_sym p x y : veq p x y -> veq p y x.
Proof. intros H b. apply cg_sym. apply H. Qed.

Lemma veq_trans p x y z : veq p x y -> veq p y z -> veq p x z.
Proof. intros H1 H2 b. eapply cg_trans; [apply H1 | apply H2]. Qed.

#[export] Instance veq_Equiv (p : Z) : Equivalence (veq p).
Proof. constructor; [exact (veq_refl p) | exact (veq_sym p) | exact (veq_trans p)]. Qed.

Lemma nth_nil_Z (b : nat) : nth b ([] : list Z) 0 = 0.
Proof. destruct b; reflexivity. Qed.

Lemma nth_vadd p x y b : cg p (nth b (vadd p x y) 0) (nth b x 0 + nth b y 0).
Proof.
  revert y b. induction x as [|a x IH]; intros y b.
  - simpl vadd. rewrite nth_nil_Z, Z.add_0_l. apply cg_refl.
  - destruct y as [|c y].
    + simpl vadd. rewrite nth_nil_Z, Z.add_0_r. apply cg_refl.
    + destruct b as [|b].
      * simpl. apply cg_mod.
      * simpl. apply IH.
Qed.

Lemma nth_vscale p c x b : cg p (nth b (vscale p c x) 0) (c * nth b x 0).
Proof.
  revert b. induction x as [|a x IH]; intros b.
  - simpl vscale. rewrite !nth_nil_Z, Z.mul_0_r. apply cg_refl.
  - destruct b as [|b].
    + simpl. apply cg_mod.
    + simpl. apply IH.
Qed.

Lemma nth_mv p M x b :
  nth b (mv p M x) 0 = ksum (nth b M []) (xnth x) mod p.
Proof.
  unfold mv, mvt. revert b. induction M as [|r M IH]; intros b.
  - destruct b; reflexivity.
  - destruct b as [|b]; simpl.
    + f_equal. apply ksum_ext. intros c. apply tget_xnth.
    + apply IH.
Qed.

#[export] Instance vadd_Proper (p : Z) : Proper (veq p ==> veq p ==> veq p) (vadd p).
Proof.
  intros x x' Hx y y' Hy b.
  eapply cg_trans; [apply nth_vadd|].
  eapply cg_trans; [|apply cg_sym; apply nth_vadd].
  apply cg_add; [apply Hx | apply Hy].
Qed.

#[export] Instance vscale_Proper (p : Z) : Proper (cg p ==> veq p ==> veq p) (vscale p).
Proof.
  intros c c' Hc x x' Hx b.
  eapply cg_trans; [apply nth_vscale|].
  eapply cg_trans; [|apply cg_sym; apply nth_vscale].
  apply cg_mul; [exact Hc | apply Hx].
Qed.

Lemma veq_nil_nth p x : veq p x [] -> forall b, cg p (nth b x 0) 0.
Proof. intros H b. specialize (H b). rewrite nth_nil_Z in H. exact H. Qed.

Lemma veq_nil_intro p x : (forall b, cg p (nth b x 0) 0) -> veq p x [].
Proof. intros H b. rewrite nth_nil_Z. apply H. Qed.

(** Linear maps on vectors, up to congruence. *)

Definition lin (p : Z) (f : vec -> vec) : Prop :=
  (forall x y, veq p x y -> veq p (f x) (f y)) /\
  (forall x y, veq p (f (vadd p x y)) (vadd p (f x) (f y))) /\
  (forall c x, veq p (f (vscale p c x)) (vscale p c (f x))).

Lemma lin_proper p f : lin p f -> forall x y, veq p x y -> veq p (f x) (f y).
Proof. intros [H _]. exact H. Qed.

Lemma lin_zero p f : lin p f -> forall x, veq p x [] -> veq p (f x) [].
Proof.
  intros Hl x Hx.
  destruct Hl as [H1 [H2 H3]].
  assert (Hs : veq p x (vscale p 0 x)).
  { intros b. eapply cg_trans; [apply (veq_nil_nth p x Hx b)|].
    apply cg_sym. eapply cg_trans; [apply nth_vscale|]. rewrite Z.mul_0_l. apply cg_refl. }
  etransitivity; [apply H1; exact Hs|].
  etransitivity; [apply H3|].
  apply veq_nil_intro. intros b.
  eapply cg_trans; [apply nth_vscale|]. rewrite Z.mul_0_l. apply cg_refl.
Qed.

Lemma mv_nth_cg p M x b :
  cg p (nth b (mv p M x) 0) (ksum (nth b M []) (xnth x)).
Proof. rewrite nth_mv. apply cg_mod. Qed.

Lemma mv_lin p M : lin p (mv p M).
Proof.
  split; [|split].
  - intros x y H b.
    eapply cg_trans; [apply mv_nth_cg|].
    eapply cg_trans; [|apply cg_sym; apply mv_nth_cg].
    apply ksum_cg. intros c. exact (H (ridx c)).
  - intros x y b.
    eapply cg_trans; [apply mv_nth_cg|].
    eapply cg_trans; [|apply cg_sym; apply nth_vadd].
    eapply cg_trans.
    + apply ksum_cg with (G := fun c => xnth x c + xnth y c).
      intros c. exact (nth_vadd p x y (ridx c)).
    + eapply cg_trans;
        [apply cg_eq; exact (ksum_add_fun (nth b M []) (xnth x) (xnth y))|].
      apply cg_add; apply cg_sym; apply mv_nth_cg.
  - intros c x b.
    eapply cg_trans; [apply mv_nth_cg|].
    eapply cg_trans; [|apply cg_sym; apply nth_vscale].
    eapply cg_trans.
    + apply ksum_cg with (G := fun c' => c * xnth x c').
      intros c'. exact (nth_vscale p c x (ridx c')).
    + eapply cg_trans;
        [apply cg_eq; exact (ksum_scale_fun (nth b M []) c (xnth x))|].
      apply cg_mul; [apply cg_refl | apply cg_sym; apply mv_nth_cg].
Qed.

(** * Monomials, evaluation and polynomial arithmetic *)

Definition mono := list nat.
Definition poly := list (mono * Z).

Fixpoint iter (f : vec -> vec) (k : nat) : vec -> vec :=
  match k with
  | O => fun x => x
  | S k' => fun x => f (iter f k' x)
  end.

Fixpoint mono_apply (p : Z) (ops : list spmat) (m : mono) : vec -> vec :=
  match ops, m with
  | M :: os, k :: m' => fun x => iter (mv p M) k (mono_apply p os m' x)
  | _, _ => fun x => x
  end.

Fixpoint ev (p : Z) (ops : list spmat) (f : poly) (x : vec) : vec :=
  match f with
  | [] => []
  | t :: f' => vadd p (vscale p (snd t) (mono_apply p ops (fst t) x)) (ev p ops f' x)
  end.

Fixpoint madd (a b : mono) : mono :=
  match a, b with
  | [], _ => b
  | _, [] => a
  | x :: a', y :: b' => (x + y)%nat :: madd a' b'
  end.

Lemma lin_id p : lin p (fun x => x).
Proof. split; [|split]; [intros x y H; exact H | intros x y; apply veq_refl | intros c x; apply veq_refl]. Qed.

Lemma lin_comp p f g : lin p f -> lin p g -> lin p (fun x => f (g x)).
Proof.
  intros [F1 [F2 F3]] [G1 [G2 G3]]. split; [|split].
  - intros x y H. apply F1. apply G1. exact H.
  - intros x y. etransitivity; [apply F1; apply G2 | apply F2].
  - intros c x. etransitivity; [apply F1; apply G3 | apply F3].
Qed.

Lemma lin_iter p f : lin p f -> forall k, lin p (iter f k).
Proof.
  intros Hf k. induction k as [|k IH].
  - exact (lin_id p).
  - exact (lin_comp p f (iter f k) Hf IH).
Qed.

Lemma lin_mono p ops : forall m, lin p (mono_apply p ops m).
Proof.
  induction ops as [|M os IH]; intros m.
  - destruct m; exact (lin_id p).
  - destruct m as [|k m'].
    + exact (lin_id p).
    + exact (lin_comp p (iter (mv p M) k) (mono_apply p os m') (lin_iter p _ (mv_lin p M) k) (IH m')).
Qed.

Definition commutes (p : Z) (f g : vec -> vec) : Prop := forall x, veq p (f (g x)) (g (f x)).

Lemma commutes_sym p f g : commutes p f g -> commutes p g f.
Proof. intros H x. symmetry. apply H. Qed.

Lemma commutes_iter p f g : lin p f -> commutes p f g -> forall k, commutes p (iter f k) g.
Proof.
  intros Hl Hc k. induction k as [|k IH]; intros x; simpl.
  - apply veq_refl.
  - etransitivity; [apply (lin_proper p f Hl); apply IH|]. apply Hc.
Qed.

Lemma commutes_comp p f g h : lin p g -> commutes p f g -> commutes p f h ->
  commutes p f (fun x => g (h x)).
Proof.
  intros Hg Hfg Hfh x.
  etransitivity; [apply Hfg|].
  apply (lin_proper p g Hg). apply Hfh.
Qed.

Definition pcomm (p : Z) (ops : list spmat) : Prop :=
  forall M N, In M ops -> In N ops -> commutes p (mv p M) (mv p N).

Lemma mono_comm p M ops : forall m,
  (forall N, In N ops -> commutes p (mv p M) (mv p N)) ->
  commutes p (mv p M) (mono_apply p ops m).
Proof.
  induction ops as [|N os IH]; intros m H.
  - destruct m; intros x; apply veq_refl.
  - destruct m as [|k m'].
    + intros x. apply veq_refl.
    + change (commutes p (mv p M) (fun x => iter (mv p N) k (mono_apply p os m' x))).
      apply commutes_comp.
      * apply lin_iter. apply mv_lin.
      * apply commutes_sym. apply commutes_iter; [apply mv_lin|].
        apply commutes_sym. apply H. left. reflexivity.
      * apply IH. intros N' HN'. apply H. right. exact HN'.
Qed.

Lemma iter_add f k l x : iter f (k + l) x = iter f k (iter f l x).
Proof. induction k as [|k IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma mono_madd p ops : pcomm p ops -> forall m1 m2 x,
  veq p (mono_apply p ops (madd m1 m2) x)
        (mono_apply p ops m1 (mono_apply p ops m2 x)).
Proof.
  induction ops as [|M os IH]; intros Hc m1 m2 x.
  - apply veq_refl.
  - destruct m1 as [|k m1'].
    + apply veq_refl.
    + destruct m2 as [|l m2'].
      * apply veq_refl.
      * change (veq p (iter (mv p M) (k + l) (mono_apply p os (madd m1' m2') x))
                      (iter (mv p M) k (mono_apply p os m1'
                         (iter (mv p M) l (mono_apply p os m2' x))))).
        assert (Hc' : pcomm p os) by (intros M' N' HM HN; apply Hc; right; assumption).
        etransitivity.
        { apply (lin_proper p _ (lin_iter p (mv p M) (mv_lin p M) (k + l))).
          apply (IH Hc' m1' m2' x). }
        rewrite iter_add.
        apply (lin_proper p _ (lin_iter p (mv p M) (mv_lin p M) k)).
        apply (commutes_iter p (mv p M) (mono_apply p os m1') (mv_lin p M)
                 (mono_comm p M os m1' (fun N HN => Hc M N (or_introl eq_refl) (or_intror HN))) l
                 (mono_apply p os m2' x)).
Qed.

Lemma ev_nth p ops f x b :
  cg p (nth b (ev p ops f x) 0) (ksum f (fun m => nth b (mono_apply p ops m x) 0)).
Proof.
  induction f as [|t f IH].
  - simpl ev. simpl ksum. rewrite nth_nil_Z. apply cg_refl.
  - simpl ev. simpl ksum.
    eapply cg_trans; [apply nth_vadd|].
    apply cg_add; [apply nth_vscale | exact IH].
Qed.

Lemma ev_app p ops f g x :
  veq p (ev p ops (f ++ g) x) (vadd p (ev p ops f x) (ev p ops g x)).
Proof.
  intros b.
  eapply cg_trans; [apply ev_nth|].
  eapply cg_trans; [|apply cg_sym; apply nth_vadd].
  rewrite ksum_app.
  apply cg_add; apply cg_sym; apply ev_nth.
Qed.

Lemma ev_lin p ops f : lin p (ev p ops f).
Proof.
  split; [|split].
  - intros x y H b.
    eapply cg_trans; [apply ev_nth|].
    eapply cg_trans; [|apply cg_sym; apply ev_nth].
    apply ksum_cg. intros m. exact (lin_proper p _ (lin_mono p ops m) x y H b).
  - intros x y b.
    eapply cg_trans; [apply ev_nth|].
    eapply cg_trans; [|apply cg_sym; apply nth_vadd].
    eapply cg_trans.
    + apply ksum_cg with (G := fun m => nth b (mono_apply p ops m x) 0 + nth b (mono_apply p ops m y) 0).
      intros m. destruct (lin_mono p ops m) as [_ [H2 _]].
      eapply cg_trans; [apply (H2 x y b)|]. apply nth_vadd.
    + eapply cg_trans;
        [apply cg_eq; exact (ksum_add_fun f (fun m => nth b (mono_apply p ops m x) 0)
                               (fun m => nth b (mono_apply p ops m y) 0))|].
      apply cg_add; apply cg_sym; apply ev_nth.
  - intros c x b.
    eapply cg_trans; [apply ev_nth|].
    eapply cg_trans; [|apply cg_sym; apply nth_vscale].
    eapply cg_trans.
    + apply ksum_cg with (G := fun m => c * nth b (mono_apply p ops m x) 0).
      intros m. destruct (lin_mono p ops m) as [_ [_ H3]].
      eapply cg_trans; [apply (H3 c x b)|]. apply nth_vscale.
    + eapply cg_trans;
        [apply cg_eq; exact (ksum_scale_fun f c (fun m => nth b (mono_apply p ops m x) 0))|].
      apply cg_mul; [apply cg_refl | apply cg_sym; apply ev_nth].
Qed.

Definition padd (f g : poly) : poly := f ++ g.

Definition pneg (f : poly) : poly := map (fun t => (fst t, - snd t)) f.

Definition pmul (f g : poly) : poly :=
  flat_map (fun s => map (fun t => (madd (fst s) (fst t), snd s * snd t)) g) f.

Definition one_poly (n : nat) : poly := [(repeat 0%nat n, 1)].

Fixpoint unit_mono (n k : nat) : mono :=
  match n, k with
  | O, _ => []
  | S n', O => 1%nat :: repeat 0%nat n'
  | S n', S k' => 0%nat :: unit_mono n' k'
  end.

Definition var (n k : nat) : poly := [(unit_mono n k, 1)].

Fixpoint lincomb (cs : list Z) (Ps : list poly) : poly :=
  match cs, Ps with
  | c :: cs', P :: Ps' => map (fun t => (fst t, c * snd t)) P ++ lincomb cs' Ps'
  | _, _ => []
  end.

Fixpoint combo (cs gs : list poly) : poly :=
  match cs, gs with
  | c :: cs', g :: gs' => pmul c g ++ combo cs' gs'
  | _, _ => []
  end.

Definition mono_eq_dec : forall a b : mono, {a = b} + {a <> b} := list_eq_dec Nat.eq_dec.

Definition pcoef (f : poly) (m : mono) : Z := kcoef mono_eq_dec f m.

Definition pzero (p : Z) (f : poly) : Prop := forall m, cg p (pcoef f m) 0.

Definition wf_poly (n : nat) (f : poly) : Prop := Forall (fun t => length (fst t) = n) f.

Fixpoint const_coef (f : poly) : Z :=
  match f with
  | [] => 0
  | t :: f' => (if forallb (Nat.eqb 0%nat) (fst t) then snd t else 0) + const_coef f'
  end.

Lemma pzero_diff p ops A R x :
  pzero p (padd A (pneg R)) -> veq p (ev p ops A x) (ev p ops R x).
Proof.
  intros Hz b.
  eapply cg_trans; [apply ev_nth|].
  eapply cg_trans; [|apply cg_sym; apply ev_nth].
  set (F := fun m => nth b (mono_apply p ops m x) 0).
  assert (H0 : cg p (ksum (A ++ pneg R) F) 0).
  { apply (ksum_zero_keys mono_eq_dec). intros k _. apply Hz. }
  rewrite ksum_app in H0. unfold pneg in H0. rewrite ksum_neg_list in H0.
  unfold cg in *.
  replace (ksum A F - ksum R F) with (ksum A F + - ksum R F - 0) by ring.
  exact H0.
Qed.

Lemma ev_scale p ops c P y :
  veq p (ev p ops (map (fun t => (fst t, c * snd t)) P) y) (vscale p c (ev p ops P y)).
Proof.
  intros b.
  eapply cg_trans; [apply ev_nth|].
  eapply cg_trans; [|apply cg_sym; apply nth_vscale].
  rewrite ksum_scale_list.
  apply cg_mul; [apply cg_refl | apply cg_sym; apply ev_nth].
Qed.

Lemma mono_ev p ops ms g y b :
  cg p (nth b (mono_apply p ops ms (ev p ops g y)) 0)
       (ksum g (fun mt => nth b (mono_apply p ops ms (mono_apply p ops mt y)) 0)).
Proof.
  induction g as [|t g IH].
  - simpl ev. simpl ksum.
    pose proof (lin_zero p _ (lin_mono p ops ms) [] (veq_refl p [])) as H0.
    specialize (H0 b). rewrite nth_nil_Z in H0. exact H0.
  - simpl ev. simpl ksum.
    destruct (lin_mono p ops ms) as [Hp [Ha Hs]].
    eapply cg_trans; [apply (Ha _ _ b)|].
    eapply cg_trans; [apply nth_vadd|].
    apply cg_add.
    + eapply cg_trans; [apply (Hs _ _ b)|]. apply nth_vscale.
    + exact IH.
Qed.

Lemma ksum_map_madd p ops (Hc : pcomm p ops) ms cs y b g :
  cg p (ksum (map (fun t => (madd ms (fst t), cs * snd t)) g)
             (fun m => nth b (mono_apply p ops m y) 0))
       (cs * ksum g (fun mt => nth b (mono_apply p ops ms (mono_apply p ops mt y)) 0)).
Proof.
  induction g as [|t g IH].
  - simpl map. simpl ksum. rewrite Z.mul_0_r. apply cg_refl.
  - simpl map. simpl ksum.
    assert (Hm : cg p (nth b (mono_apply p ops (madd ms (fst t)) y) 0)
                      (nth b (mono_apply p ops ms (mono_apply p ops (fst t) y)) 0))
      by apply (mono_madd p ops Hc ms (fst t) y b).
    eapply cg_trans; [apply cg_add; [apply cg_mul; [apply cg_refl | exact Hm] | exact IH]|].
    apply cg_eq. ring.
Qed.

Lemma ev_map_mul p ops (Hc : pcomm p ops) ms cs g y :
  veq p (ev p ops (map (fun t => (madd ms (fst t), cs * snd t)) g) y)
        (vscale p cs (mono_apply p ops ms (ev p ops g y))).
Proof.
  intros b.
  eapply cg_trans; [apply ev_nth|].
  eapply cg_trans; [apply ksum_map_madd; exact Hc|].
  eapply cg_trans; [|apply cg_sym; apply nth_vscale].
  apply cg_mul; [apply cg_refl | apply cg_sym; apply mono_ev].
Qed.

Lemma ev_pmul p ops (Hc : pcomm p ops) f g y :
  veq p (ev p ops (pmul f g) y) (ev p ops f (ev p ops g y)).
Proof.
  induction f as [|s f IH].
  - apply veq_refl.
  - change (pmul (s :: f) g)
      with (map (fun t => (madd (fst s) (fst t), snd s * snd t)) g ++ pmul f g).
    etransitivity; [apply ev_app|].
    change (ev p ops (s :: f) (ev p ops g y))
      with (vadd p (vscale p (snd s) (mono_apply p ops (fst s) (ev p ops g y)))
                   (ev p ops f (ev p ops g y))).
    exact (vadd_Proper p _ _ (ev_map_mul p ops Hc (fst s) (snd s) g y) _ _ IH).
Qed.

Lemma ev_combo_zero p ops (Hc : pcomm p ops) y : forall cs gs,
  Forall (fun g => veq p (ev p ops g y) []) gs -> veq p (ev p ops (combo cs gs) y) [].
Proof.
  induction cs as [|c cs IH]; intros gs Hf; destruct gs as [|g gs]; try (simpl; apply veq_refl).
  simpl combo. inversion Hf as [|? ? Hg Hgs]; subst.
  etransitivity; [apply ev_app|].
  assert (H1 : veq p (ev p ops (pmul c g) y) []).
  { etransitivity; [apply ev_pmul; exact Hc|].
    apply (lin_zero p _ (ev_lin p ops c)). exact Hg. }
  rewrite H1, (IH gs Hgs). simpl vadd. apply veq_refl.
Qed.

(** * Products, certificates and the checker *)

Fixpoint shift (o : nat) (l : list Z) : list Z :=
  match o with
  | O => l
  | S o' => 0 :: shift o' l
  end.

Fixpoint mset_aux {A : Type} (mulg : poly -> A -> A) (F : list poly -> list A)
  (G : list poly) : list A :=
  match G with
  | [] => []
  | g :: G' => map (mulg g) (F G) ++ mset_aux mulg F G'
  end.

Fixpoint msets {A : Type} (mulg : poly -> A -> A) (one : A) (d : nat)
  : list poly -> list A :=
  match d with
  | O => fun _ => [one]
  | S d' => fun G => mset_aux mulg (msets mulg one d') G
  end.

Definition products (n : nat) (G : list poly) (d : nat) : list poly :=
  msets pmul (one_poly n) d G.

Definition m_products (n : nat) (G : list poly) (d : nat) : list poly :=
  flat_map (fun k => map (pmul (var n k)) (products n G d)) (seq 0 n).

Definition select_products (n : nat) (G : list poly) (d : nat) (sel : list nat) : list poly :=
  map (fun i => nth i (products n G d) (one_poly n)) sel.

Definition in_local_ideal (p : Z) (n : nat) (gens : list poly) (f : poly) : Prop :=
  exists u cofs, wf_poly n u /\ Forall (wf_poly n) cofs /\ length cofs = length gens /\
    ~ cg p (const_coef u) 0 /\ pzero p (padd (pmul u f) (pneg (combo cofs gens))).

Definition independent_mod (p : Z) (n : nat) (gens reps : list poly) : Prop :=
  forall cs, length cs = length reps -> in_local_ideal p n gens (lincomb cs reps) ->
    Forall (fun c => cg p c 0) cs.

Definition spans_mod (p : Z) (n : nat) (gens S reps : list poly) : Prop :=
  forall rho, In rho S -> exists cs, length cs = length reps /\
    in_local_ideal p n gens (padd rho (pneg (lincomb cs reps))).

Definition hilbert_cell (p : Z) (n : nat) (J G : list poly) (d r : nat) : Prop :=
  exists sel, length sel = r /\
    (forall i, In i sel -> (i < length (products n G d))%nat) /\
    independent_mod p n (J ++ m_products n G d) (select_products n G d sel) /\
    spans_mod p n (J ++ m_products n G d) (products n G d) (select_products n G d sel).

Definition vzero_b (p : Z) (x : vec) : bool := forallb (fun a => Z.eqb (a mod p) 0) x.

Definition rowprod (M N : spmat) (b : nat) : row :=
  flat_map (fun cv => map (fun t => (fst t, snd cv * snd t)) (nth (ridx (fst cv)) N [])) (nth b M []).

Definition rowdiff_b (p : Z) (R1 R2 : row) : bool :=
  let L := R1 ++ map (fun t => (fst t, - snd t)) R2 in
  forallb (fun c => Z.eqb (kcoef Pos.eq_dec L c mod p) 0) (map fst L).

Definition comm_b (p : Z) (M N : spmat) : bool :=
  forallb (fun b => rowdiff_b p (rowprod M N b) (rowprod N M b))
    (seq 0 (Nat.max (length M) (length N))).

Definition strict_b (p : Z) (lev : list nat) (M : spmat) : bool :=
  forallb (fun b => forallb (fun cv => Z.eqb (snd cv mod p) 0 ||
                                 Nat.ltb (nth (ridx (fst cv)) lev 0%nat) (nth b lev 0%nat))
                      (nth b M []))
    (seq 0 (length M)).

Fixpoint left_ok (p : Z) (L : spmat) (vs : list vec) (i : nat) : bool :=
  match vs with
  | [] => true
  | v :: vs' => vzero_b p (vadd p (mv p L v) (vscale p (-1) (shift i [1]))) &&
                left_ok p L vs' (S i)
  end.

Fixpoint vstep (p : Z) (ops : list spmat) (G : list poly) (prev : list (list vec))
  : list (list vec) :=
  match G, prev with
  | g :: G', pg :: prev' =>
      let rest := vstep p ops G' prev' in
      (map (fun v => ev p ops g v) pg ++ nth 0 rest []) :: rest
  | _, _ => [[]]
  end.

Fixpoint vlevels (p : Z) (ops : list spmat) (e : vec) (G : list poly) (d : nat)
  : list (list vec) :=
  match d with
  | O => repeat [e] (S (length G))
  | S d' => vstep p ops G (vlevels p ops e G d')
  end.

Definition pvecs (p : Z) (ops : list spmat) (e : vec) (G : list poly) (d : nat) : list vec :=
  nth 0 (vlevels p ops e G d) [].

Record cert := mk_cert {
  c_ops : list spmat;
  c_lev : list nat;
  c_e : vec;
  c_left : spmat;
  c_sel : list nat }.

Definition check_cert (p : Z) (n : nat) (J G : list poly) (d : nat) (c : cert) : bool :=
  let ops := c_ops c in
  let PV := pvecs p ops (c_e c) G d in
  Nat.eqb (length ops) n
  && forallb (fun M => forallb (fun N => comm_b p M N) ops) ops
  && forallb (strict_b p (c_lev c)) ops
  && forallb (fun g => vzero_b p (ev p ops g (c_e c))) J
  && forallb (fun v => forallb (fun M => vzero_b p (mv p M v)) ops) PV
  && forallb (fun i => Nat.ltb i (length PV)) (c_sel c)
  && left_ok p (c_left c) (map (fun i => nth i PV (c_e c)) (c_sel c)) 0.

(** * Calibration: a two-variable cell over F_7 *)

Definition toy_J : list poly := [ [([2%nat; 0%nat], 1)]; [([0%nat; 2%nat], 1)] ].
Definition toy_G : list poly := [ [([1%nat; 0%nat], 1)]; [([0%nat; 1%nat], 3)] ].

Definition toy_cert : cert :=
  mk_cert
    [ [ []; [(1%positive, 1)]; [] ]; [ []; []; [(1%positive, 1)] ] ]
    [0%nat; 1%nat; 1%nat]
    [1; 0; 0]
    [ [(2%positive, 1)]; [(3%positive, 5)] ]
    [0%nat; 1%nat].

Lemma toy_cert_accepted : check_cert 7 2 toy_J toy_G 1 toy_cert = true.
Proof. vm_compute. reflexivity. Qed.

Definition toy_left_mutant : cert :=
  mk_cert (c_ops toy_cert) (c_lev toy_cert) (c_e toy_cert)
    [ [(2%positive, 1)]; [(3%positive, 4)] ] (c_sel toy_cert).

Lemma toy_left_mutant_rejected : check_cert 7 2 toy_J toy_G 1 toy_left_mutant = false.
Proof. vm_compute. reflexivity. Qed.

Definition toy_comm_mutant : cert :=
  mk_cert [ [ []; [(1%positive, 1)]; [] ]; [ []; [(1%positive, 1)]; [(1%positive, 1)] ] ]
    (c_lev toy_cert) (c_e toy_cert) (c_left toy_cert) (c_sel toy_cert).

Lemma toy_comm_mutant_rejected : check_cert 7 2 toy_J toy_G 1 toy_comm_mutant = false.
Proof. vm_compute. reflexivity. Qed.

Definition toy_level_mutant : cert :=
  mk_cert (c_ops toy_cert) [0%nat; 1%nat; 0%nat] (c_e toy_cert) (c_left toy_cert) (c_sel toy_cert).

Lemma toy_level_mutant_rejected : check_cert 7 2 toy_J toy_G 1 toy_level_mutant = false.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_generator_mutant_rejected :
  check_cert 7 2 ([([1%nat; 0%nat], 1)] :: toy_J) toy_G 1 toy_cert = false.
Proof. vm_compute. reflexivity. Qed.


Lemma toy_product_mutant_rejected :
  check_cert 7 2 toy_J ([([1%nat; 0%nat], 1)] :: toy_G) 1 toy_cert = false.
Proof. vm_compute. reflexivity. Qed.

(** * Soundness of the checker *)

Lemma vadd_nil_r p x : vadd p x [] = x.
Proof. destruct x; reflexivity. Qed.

Lemma nth_vadd_scale p c x y b :
  cg p (nth b (vadd p (vscale p c x) y) 0) (c * nth b x 0 + nth b y 0).
Proof.
  eapply cg_trans; [apply nth_vadd|].
  apply cg_add; [apply nth_vscale | apply cg_refl].
Qed.

Lemma veq_of_vsub p x y : veq p (vadd p x (vscale p (-1) y)) [] -> veq p x y.
Proof.
  intros H b. pose proof (H b) as Hb. rewrite nth_nil_Z in Hb.
  assert (H2 : cg p (nth b x 0 + (-1) * nth b y 0) 0).
  { eapply cg_trans; [|exact Hb]. apply cg_sym.
    eapply cg_trans; [apply nth_vadd|].
    apply cg_add; [apply cg_refl | apply nth_vscale]. }
  unfold cg in *.
  replace (nth b x 0 - nth b y 0) with (nth b x 0 + (-1) * nth b y 0 - 0) by ring.
  exact H2.
Qed.

Lemma vzero_b_sound p x : vzero_b p x = true -> veq p x [].
Proof.
  intros H b. rewrite nth_nil_Z. unfold vzero_b in H. rewrite forallb_forall in H.
  destruct (Nat.lt_ge_cases b (length x)) as [Hl|Hl].
  - apply cg_zero_of_mod. apply Z.eqb_eq. apply H. apply nth_In. exact Hl.
  - rewrite nth_overflow by exact Hl. apply cg_refl.
Qed.

Lemma rowdiff_sound p R1 R2 : rowdiff_b p R1 R2 = true ->
  forall F, cg p (ksum R1 F) (ksum R2 F).
Proof.
  intros H F. unfold rowdiff_b in H. rewrite forallb_forall in H.
  assert (H0 : cg p (ksum (R1 ++ map (fun t => (fst t, - snd t)) R2) F) 0).
  { apply (ksum_zero_keys Pos.eq_dec). intros k Hk. apply cg_zero_of_mod.
    apply Z.eqb_eq. apply H. exact Hk. }
  rewrite ksum_app, ksum_neg_list in H0. unfold cg in *.
  replace (ksum R1 F - ksum R2 F) with (ksum R1 F + - ksum R2 F - 0) by ring.
  exact H0.
Qed.

Lemma ksum_rowprod (rA : row) (N : spmat) F :
  ksum (flat_map (fun cv => map (fun t => (fst t, snd cv * snd t)) (nth (ridx (fst cv)) N [])) rA) F
  = ksum rA (fun c => ksum (nth (ridx c) N []) F).
Proof.
  induction rA as [|cv rA IH]; simpl; [reflexivity|].
  rewrite ksum_app, ksum_scale_list, IH. reflexivity.
Qed.

Lemma mv_mv_nth p M N x b :
  cg p (nth b (mv p M (mv p N x)) 0) (ksum (rowprod M N b) (xnth x)).
Proof.
  eapply cg_trans; [apply mv_nth_cg|].
  unfold rowprod. rewrite ksum_rowprod.
  apply ksum_cg. intros c. apply mv_nth_cg.
Qed.

Lemma comm_b_sound p M N : comm_b p M N = true -> commutes p (mv p M) (mv p N).
Proof.
  intros H x b.
  eapply cg_trans; [apply mv_mv_nth|].
  eapply cg_trans; [|apply cg_sym; apply mv_mv_nth].
  destruct (Nat.lt_ge_cases b (Nat.max (length M) (length N))) as [Hl|Hl].
  - unfold comm_b in H. rewrite forallb_forall in H.
    apply rowdiff_sound. apply H. apply (proj2 (in_seq _ _ _)). lia.
  - assert (HM : nth b M [] = []) by (apply nth_overflow; lia).
    assert (HN : nth b N [] = []) by (apply nth_overflow; lia).
    unfold rowprod. rewrite HM, HN. simpl. apply cg_refl.
Qed.

Definition Vanish (p : Z) (lev : list nat) (L : nat) (y : vec) : Prop :=
  forall c, (nth c lev 0%nat < L)%nat -> cg p (nth c y 0) 0.

Definition strict_mat (p : Z) (lev : list nat) (M : spmat) : Prop :=
  forall b cv, In cv (nth b M []) ->
    (nth (ridx (fst cv)) lev 0%nat < nth b lev 0%nat)%nat \/ cg p (snd cv) 0.

Lemma strict_b_sound p lev M : strict_b p lev M = true -> strict_mat p lev M.
Proof.
  intros H b cv Hin. unfold strict_b in H. rewrite forallb_forall in H.
  destruct (Nat.lt_ge_cases b (length M)) as [Hl|Hl].
  - specialize (H b (proj2 (in_seq (length M) 0 b) (conj (Nat.le_0_l b) Hl))).
    rewrite forallb_forall in H. specialize (H cv Hin).
    apply orb_true_iff in H as [H|H].
    + right. apply cg_zero_of_mod. apply Z.eqb_eq. exact H.
    + left. apply Nat.ltb_lt. exact H.
  - rewrite (nth_overflow M [] Hl) in Hin. destruct Hin.
Qed.

Lemma Vanish_le p lev L L' y : (L <= L')%nat -> Vanish p lev L' y -> Vanish p lev L y.
Proof. intros H Hy c Hc. apply Hy. lia. Qed.

Lemma mv_strict p lev M : strict_mat p lev M ->
  forall L y, Vanish p lev L y -> Vanish p lev (S L) (mv p M y).
Proof.
  intros Hs L y Hy b Hb.
  eapply cg_trans; [apply mv_nth_cg|].
  apply ksum_zero_terms. intros cv Hcv.
  destruct (Hs b cv Hcv) as [Hl|Hz].
  - apply cg_zero_mul_r. apply Hy. lia.
  - apply cg_zero_mul_l. exact Hz.
Qed.

Lemma iter_preserve p lev M : strict_mat p lev M ->
  forall k L y, Vanish p lev L y -> Vanish p lev L (iter (mv p M) k y).
Proof.
  intros Hs k. induction k as [|k IH]; intros L y Hy; [exact Hy|].
  simpl. apply (Vanish_le p lev L (S L)); [lia|].
  apply mv_strict; [exact Hs|]. apply IH. exact Hy.
Qed.

Lemma mono_preserve p lev ops : Forall (strict_mat p lev) ops ->
  forall m L y, Vanish p lev L y -> Vanish p lev L (mono_apply p ops m y).
Proof.
  induction ops as [|M os IH]; intros Hs m L y Hy; [destruct m; exact Hy|].
  inversion Hs as [|? ? HM Hos]; subst.
  destruct m as [|k m']; [exact Hy|].
  simpl. apply iter_preserve; [exact HM|]. apply IH; assumption.
Qed.

Lemma mono_strict p lev ops : Forall (strict_mat p lev) ops ->
  forall m, length m = length ops -> forallb (Nat.eqb 0%nat) m = false ->
  forall L y, Vanish p lev L y -> Vanish p lev (S L) (mono_apply p ops m y).
Proof.
  induction ops as [|M os IH]; intros Hs m Hlen Hf L y Hy.
  - destruct m; [|discriminate]. simpl in Hf. discriminate.
  - inversion Hs as [|? ? HM Hos]; subst.
    destruct m as [|k m']; [discriminate|].
    simpl in Hlen. injection Hlen as Hlen.
    simpl in Hf. apply andb_false_iff in Hf as [Hk|Hm'].
    + destruct k as [|k]; [discriminate|].
      simpl. apply mv_strict; [exact HM|].
      apply iter_preserve; [exact HM|]. apply mono_preserve; assumption.
    + simpl. apply iter_preserve; [exact HM|]. apply IH; assumption.
Qed.

Lemma mono_one p ops : forall m y,
  forallb (Nat.eqb 0%nat) m = true -> mono_apply p ops m y = y.
Proof.
  induction ops as [|M os IH]; intros m y H; [destruct m; reflexivity|].
  destruct m as [|k m']; [reflexivity|].
  simpl in H. apply andb_true_iff in H as [Hk Hm'].
  destruct k as [|k]; [|discriminate].
  simpl. rewrite (IH m' y Hm'). reflexivity.
Qed.

Lemma ev_const p lev ops (Hs : Forall (strict_mat p lev) ops) u :
  Forall (fun t => length (fst t) = length ops) u ->
  forall L y c, Vanish p lev L y -> nth c lev 0%nat = L ->
  cg p (nth c (ev p ops u y) 0) (const_coef u * nth c y 0).
Proof.
  induction u as [|t u IH]; intros Hwf L y c Hy Hc.
  - simpl ev. simpl const_coef. rewrite nth_nil_Z, Z.mul_0_l. apply cg_refl.
  - pose proof (Forall_inv Hwf) as Ht. pose proof (Forall_inv_tail Hwf) as Hwf'.
    simpl in Ht.
    change (ev p ops (t :: u) y)
      with (vadd p (vscale p (snd t) (mono_apply p ops (fst t) y)) (ev p ops u y)).
    change (const_coef (t :: u))
      with ((if forallb (Nat.eqb 0%nat) (fst t) then snd t else 0) + const_coef u).
    eapply cg_trans; [apply nth_vadd|].
    destruct (forallb (Nat.eqb 0%nat) (fst t)) eqn:Hf.
    + assert (Hm : mono_apply p ops (fst t) y = y) by (apply mono_one; exact Hf).
      eapply cg_trans;
        [apply cg_add;
         [eapply cg_trans; [apply nth_vscale | apply cg_mul; [apply cg_refl | rewrite Hm; apply cg_refl]]
         | apply (IH Hwf' L y c Hy Hc)]|].
      cbv iota. apply cg_eq. ring.
    + assert (Hv : Vanish p lev (S L) (mono_apply p ops (fst t) y))
        by (apply mono_strict; assumption).
      assert (Hz : cg p (snd t * nth c (mono_apply p ops (fst t) y) 0) 0).
      { apply cg_zero_mul_r. apply Hv. lia. }
      eapply cg_trans;
        [apply cg_add;
         [eapply cg_trans; [apply nth_vscale | exact Hz]
         | apply (IH Hwf' L y c Hy Hc)]|].
      cbv iota. apply cg_eq. ring.
Qed.

Lemma ev_inj p lev ops (Hprime : prime p) (Hs : Forall (strict_mat p lev) ops) u :
  wf_poly (length ops) u -> ~ cg p (const_coef u) 0 ->
  forall y, veq p (ev p ops u y) [] -> veq p y [].
Proof.
  intros Hwf Hnz y Hy.
  assert (HV : forall L, Vanish p lev L y).
  { induction L as [|L IH].
    - intros c Hc. exfalso. lia.
    - intros c Hc.
      destruct (Nat.lt_ge_cases (nth c lev 0%nat) L) as [Hlt|Hge].
      + apply IH. exact Hlt.
      + assert (Hc' : nth c lev 0%nat = L) by lia.
        pose proof (ev_const p lev ops Hs u Hwf L y c IH Hc') as H1.
        pose proof (veq_nil_nth p _ Hy c) as H2.
        assert (H3 : cg p (const_coef u * nth c y 0) 0)
          by (eapply cg_trans; [apply cg_sym; exact H1 | exact H2]).
        unfold cg in H3. rewrite Z.sub_0_r in H3.
        apply (proj1 (Z.divide_prime_mul _ _ _ (proj2 (prime_alt p) Hprime))) in H3.
        destruct H3 as [H3|H3].
        * exfalso. apply Hnz. unfold cg. rewrite Z.sub_0_r. exact H3.
        * unfold cg. rewrite Z.sub_0_r. exact H3. }
  intros b. rewrite nth_nil_Z.
  exact (HV (S (nth b lev 0%nat)) b (Nat.lt_succ_diag_r _)).
Qed.

Lemma mono_zero p ops n y : mono_apply p ops (repeat 0%nat n) y = y.
Proof.
  revert n. induction ops as [|M os IH]; intros n; [destruct n; reflexivity|].
  destruct n as [|n]; [reflexivity|].
  simpl. rewrite IH. reflexivity.
Qed.

Lemma mono_unit p ops : forall k, (k < length ops)%nat -> forall y,
  veq p (mono_apply p ops (unit_mono (length ops) k) y) (mv p (nth k ops []) y).
Proof.
  induction ops as [|M os IH]; intros k Hk y; [simpl in Hk; lia|].
  destruct k as [|k].
  - simpl. rewrite mono_zero. apply veq_refl.
  - simpl. apply IH. simpl in Hk. lia.
Qed.

Lemma ev_one p ops n e : veq p e (ev p ops (one_poly n) e).
Proof.
  unfold one_poly. simpl ev. rewrite mono_zero, vadd_nil_r.
  intros b. apply cg_sym. eapply cg_trans; [apply nth_vscale|].
  rewrite Z.mul_1_l. apply cg_refl.
Qed.

Lemma ev_var p ops n k v :
  veq p (ev p ops (var n k) v) (mono_apply p ops (unit_mono n k) v).
Proof.
  unfold var. simpl ev. rewrite vadd_nil_r.
  intros b. eapply cg_trans; [apply nth_vscale|].
  rewrite Z.mul_1_l. apply cg_refl.
Qed.

Lemma nth_shift_lt o l b : (b < o)%nat -> nth b (shift o l) 0 = 0.
Proof.
  revert b. induction o as [|o IH]; intros b Hb; [lia|].
  destruct b as [|b]; [reflexivity|]. simpl. apply IH. lia.
Qed.

Lemma nth_shift_ge o l b : (o <= b)%nat -> nth b (shift o l) 0 = nth (b - o) l 0.
Proof.
  revert b. induction o as [|o IH]; intros b Hb;
    [rewrite Nat.sub_0_r; reflexivity|].
  destruct b as [|b]; [lia|]. simpl. apply IH. lia.
Qed.

Lemma shift_cons p c o cs :
  veq p (vadd p (vscale p c (shift o [1])) (shift (S o) cs)) (shift o (c :: cs)).
Proof.
  intros b.
  eapply cg_trans; [apply nth_vadd_scale|].
  destruct (Nat.lt_trichotomy b o) as [H|[H|H]].
  - rewrite (nth_shift_lt o [1] b H), (nth_shift_lt (S o) cs b (Nat.lt_lt_succ_r _ _ H)),
      (nth_shift_lt o (c :: cs) b H).
    apply cg_eq. ring.
  - subst b.
    rewrite (nth_shift_ge o [1] o (Nat.le_refl o)),
      (nth_shift_lt (S o) cs o (Nat.lt_succ_diag_r o)),
      (nth_shift_ge o (c :: cs) o (Nat.le_refl o)).
    rewrite Nat.sub_diag.
    change (nth 0 [1] 0) with 1. change (nth 0 (c :: cs) 0) with c.
    apply cg_eq. ring.
  - rewrite (nth_shift_ge o [1] b (Nat.lt_le_incl _ _ H)), (nth_shift_ge (S o) cs b H),
      (nth_shift_ge o (c :: cs) b (Nat.lt_le_incl _ _ H)).
    replace (b - o)%nat with (S (b - S o)) by lia.
    change (nth (S (b - S o)) [1] 0) with (nth (b - S o) ([] : list Z) 0).
    change (nth (S (b - S o)) (c :: cs) 0) with (nth (b - S o) cs 0).
    rewrite nth_nil_Z. apply cg_eq. ring.
Qed.

Lemma lincomb_left p ops (Hc : pcomm p ops) e L : forall cs Ps o,
  length cs = length Ps ->
  (forall j, (j < length Ps)%nat ->
     veq p (mv p L (ev p ops (nth j Ps []) e)) (shift (o + j) [1])) ->
  veq p (mv p L (ev p ops (lincomb cs Ps) e)) (shift o cs).
Proof.
  induction cs as [|c cs IH]; intros Ps o Hlen Hj.
  - destruct Ps as [|P Ps]; [|discriminate].
    simpl lincomb. simpl ev.
    intros b.
    pose proof (lin_zero p _ (mv_lin p L) [] (veq_refl p [])) as H0.
    specialize (H0 b). rewrite nth_nil_Z in H0.
    eapply cg_trans; [exact H0|].
    destruct (Nat.lt_ge_cases b o) as [Hb|Hb].
    + rewrite (nth_shift_lt o [] b Hb). apply cg_refl.
    + rewrite (nth_shift_ge o [] b Hb), nth_nil_Z. apply cg_refl.
  - destruct Ps as [|P Ps]; [discriminate|].
    simpl in Hlen. injection Hlen as Hlen.
    simpl lincomb.
    assert (E1 : veq p (ev p ops (map (fun t => (fst t, c * snd t)) P ++ lincomb cs Ps) e)
                       (vadd p (vscale p c (ev p ops P e)) (ev p ops (lincomb cs Ps) e))).
    { etransitivity; [apply ev_app|].
      exact (vadd_Proper p _ _ (ev_scale p ops c P e) _ _ (veq_refl p _)). }
    destruct (mv_lin p L) as [Hp [Ha Hs]].
    etransitivity; [apply Hp; exact E1|].
    etransitivity; [apply Ha|].
    assert (E2 : veq p (mv p L (ev p ops P e)) (shift o [1])).
    { pose proof (Hj 0%nat (Nat.lt_0_succ _)) as H0. simpl in H0.
      rewrite Nat.add_0_r in H0. exact H0. }
    assert (E3 : veq p (mv p L (ev p ops (lincomb cs Ps) e)) (shift (S o) cs)).
    { apply IH; [exact Hlen|]. intros j Hjl.
      assert (Hj1 : (S j < length (P :: Ps))%nat) by (simpl; lia).
      pose proof (Hj (S j) Hj1) as H0. simpl in H0.
      replace (S o + j)%nat with (o + S j)%nat by lia. exact H0. }
    etransitivity;
      [exact (vadd_Proper p _ _ (veq_trans p _ _ _ (Hs c _) (vscale_Proper p c c (cg_refl p c) _ _ E2)) _ _ E3)|].
    apply shift_cons.
Qed.

Lemma left_ok_sound p L : forall vs i, left_ok p L vs i = true ->
  forall j, (j < length vs)%nat -> veq p (mv p L (nth j vs [])) (shift (i + j) [1]).
Proof.
  induction vs as [|v vs IH]; intros i H j Hj; [simpl in Hj; lia|].
  simpl in H. apply andb_true_iff in H as [H1 H2].
  destruct j as [|j].
  - simpl. rewrite Nat.add_0_r. apply veq_of_vsub. apply vzero_b_sound. exact H1.
  - simpl. replace (i + S j)%nat with (S i + j)%nat by lia.
    apply IH; [exact H2|]. simpl in Hj. lia.
Qed.

Lemma nth_repeat_lt {A : Type} (a d : A) m k : (k < m)%nat -> nth k (repeat a m) d = a.
Proof.
  revert k. induction m as [|m IH]; intros k Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. simpl. apply IH. lia.
Qed.

Lemma vstep_length p ops G : forall prev,
  length prev = S (length G) -> length (vstep p ops G prev) = S (length G).
Proof.
  induction G as [|g G IH]; intros prev H; [reflexivity|].
  destruct prev as [|pg prev]; [discriminate|].
  simpl in H. injection H as H. simpl. rewrite (IH prev H). reflexivity.
Qed.

Lemma vlevels_length p ops e G : forall d, length (vlevels p ops e G d) = S (length G).
Proof.
  induction d as [|d IH]; [apply repeat_length|].
  simpl. apply vstep_length. exact IH.
Qed.

Lemma vstep_correct p ops (F : list poly -> list vec) : forall G prev,
  length prev = S (length G) ->
  (forall k, (k <= length G)%nat -> nth k prev [] = F (skipn k G)) ->
  forall k, (k <= length G)%nat ->
    nth k (vstep p ops G prev) [] = mset_aux (fun g v => ev p ops g v) F (skipn k G).
Proof.
  induction G as [|g G IH]; intros prev Hl Hp k Hk.
  - destruct k as [|k]; [reflexivity | simpl in Hk; lia].
  - destruct prev as [|pg prev]; [discriminate|].
    simpl in Hl. injection Hl as Hl.
    assert (Hp' : forall k, (k <= length G)%nat -> nth k prev [] = F (skipn k G)).
    { intros k' Hk'. exact (Hp (S k') (le_n_S _ _ Hk')). }
    destruct k as [|k].
    + assert (Hpg : pg = F (g :: G)) by exact (Hp 0%nat (Nat.le_0_l _)).
      assert (Hr : nth 0 (vstep p ops G prev) [] = mset_aux (fun g v => ev p ops g v) F G)
        by exact (IH prev Hl Hp' 0%nat (Nat.le_0_l _)).
      simpl. rewrite Hpg, Hr. reflexivity.
    + simpl in Hk. simpl. exact (IH prev Hl Hp' k (le_S_n _ _ Hk)).
Qed.

Lemma vlevels_correct p ops e G : forall d k, (k <= length G)%nat ->
  nth k (vlevels p ops e G d) [] = msets (fun g v => ev p ops g v) e d (skipn k G).
Proof.
  induction d as [|d IH]; intros k Hk.
  - change (nth k (repeat [e] (S (length G))) []
            = msets (fun g v => ev p ops g v) e 0 (skipn k G)).
    rewrite (nth_repeat_lt [e] [] (S (length G)) k (le_n_S _ _ Hk)). reflexivity.
  - simpl. apply (vstep_correct p ops (msets (fun g v => ev p ops g v) e d));
      [apply vlevels_length | exact IH | exact Hk].
Qed.

Lemma pvecs_msets p ops e G d :
  pvecs p ops e G d = msets (fun g v => ev p ops g v) e d G.
Proof. exact (vlevels_correct p ops e G d 0%nat (Nat.le_0_l _)). Qed.

Lemma Forall2_map_rel {A B : Type} (R : A -> B -> Prop) (f : A -> A) (f' : B -> B) l l' :
  Forall2 R l l' -> (forall a b, R a b -> R (f a) (f' b)) ->
  Forall2 R (map f l) (map f' l').
Proof. intros H Hf. induction H; simpl; constructor; [apply Hf; assumption | assumption]. Qed.

Lemma msets_rel {A B : Type} (R : A -> B -> Prop) (mulA : poly -> A -> A) (mulB : poly -> B -> B)
  (oneA : A) (oneB : B) :
  R oneA oneB -> (forall g a b, R a b -> R (mulA g a) (mulB g b)) ->
  forall d G, Forall2 R (msets mulA oneA d G) (msets mulB oneB d G).
Proof.
  intros H1 H2. induction d as [|d IH]; intros G.
  - simpl. constructor; [exact H1|constructor].
  - induction G as [|g G' IHG]; [constructor|].
    change (Forall2 R (map (mulA g) (msets mulA oneA d (g :: G'))
                       ++ mset_aux mulA (msets mulA oneA d) G')
                      (map (mulB g) (msets mulB oneB d (g :: G'))
                       ++ mset_aux mulB (msets mulB oneB d) G')).
    apply Forall2_app; [|exact IHG].
    apply Forall2_map_rel; [exact (IH (g :: G'))|]. intros a b Hab. apply H2. exact Hab.
Qed.

Lemma Forall2_nth_R {A B : Type} (R : A -> B -> Prop) l l' d d' :
  Forall2 R l l' -> R d d' -> forall i, R (nth i l d) (nth i l' d').
Proof.
  intros H Hd. induction H as [|a b l1 l2 Hab Hl IH]; intros i; [destruct i; exact Hd|].
  destruct i as [|i]; [exact Hab | apply IH].
Qed.

Lemma Forall2_In_l {A B : Type} (R : A -> B -> Prop) l l' x :
  Forall2 R l l' -> In x l -> exists y, In y l' /\ R x y.
Proof.
  intros H. induction H as [|a b l1 l2 Hab Hl IH]; intros Hin; [destruct Hin|].
  destruct Hin as [E|Hin].
  - subst a. exists b. split; [left; reflexivity | exact Hab].
  - destruct (IH Hin) as [y [Hy Hr]]. exists y. split; [right; exact Hy | exact Hr].
Qed.

Lemma nth_map_in {A B : Type} (f : A -> B) (l : list A) j d d' :
  (j < length l)%nat -> nth j (map f l) d = f (nth j l d').
Proof.
  revert j. induction l as [|a l IH]; intros j Hj; [simpl in Hj; lia|].
  destruct j as [|j]; [reflexivity|]. simpl. apply IH. simpl in Hj. lia.
Qed.

Lemma Forall_nth_default {A : Type} (Q : A -> Prop) l d :
  Forall Q l -> Q d -> forall i, Q (nth i l d).
Proof.
  intros Hf Hd i. destruct (Nat.lt_ge_cases i (length l)) as [H|H].
  - apply (proj1 (Forall_forall _ _) Hf). apply nth_In. exact H.
  - rewrite nth_overflow by exact H. exact Hd.
Qed.

Theorem cert_independent p n J G d c :
  prime p -> check_cert p n J G d c = true ->
  independent_mod p n (J ++ m_products n G d) (select_products n G d (c_sel c)).
Proof.
  intros Hprime Hchk.
  unfold check_cert in Hchk. cbv zeta in Hchk.
  set (ops := c_ops c) in *. set (lev := c_lev c) in *. set (e := c_e c) in *.
  set (L := c_left c) in *. set (sel := c_sel c) in *.
  clearbody ops lev e L sel.
  apply andb_true_iff in Hchk as [Hchk Hleft].
  apply andb_true_iff in Hchk as [Hchk Hsel].
  apply andb_true_iff in Hchk as [Hchk Hd].
  apply andb_true_iff in Hchk as [Hchk HJ].
  apply andb_true_iff in Hchk as [Hchk Hstr].
  apply andb_true_iff in Hchk as [Hn Hcomm].
  apply Nat.eqb_eq in Hn. subst n.
  assert (Hpc : pcomm p ops).
  { intros M N HM HN. apply comm_b_sound.
    rewrite forallb_forall in Hcomm. specialize (Hcomm M HM).
    rewrite forallb_forall in Hcomm. exact (Hcomm N HN). }
  assert (Hst : Forall (strict_mat p lev) ops).
  { rewrite Forall_forall. intros M HM. apply strict_b_sound.
    rewrite forallb_forall in Hstr. exact (Hstr M HM). }
  assert (Hrel : Forall2 (fun (P : poly) (v : vec) => veq p v (ev p ops P e))
                   (products (length ops) G d) (pvecs p ops e G d)).
  { unfold products. rewrite pvecs_msets. apply msets_rel.
    - exact (ev_one p ops (length ops) e).
    - intros g P v Hr. simpl.
      etransitivity; [apply (lin_proper p _ (ev_lin p ops g) _ _ Hr)|].
      symmetry. apply ev_pmul. exact Hpc. }
  assert (HJ' : forall g, In g J -> veq p (ev p ops g e) []).
  { intros g Hg. rewrite forallb_forall in HJ. apply vzero_b_sound. exact (HJ g Hg). }
  assert (HPV : forall v, In v (pvecs p ops e G d) ->
                forall M, In M ops -> veq p (mv p M v) []).
  { intros v Hv M HM. rewrite forallb_forall in Hd. specialize (Hd v Hv).
    rewrite forallb_forall in Hd. apply vzero_b_sound. exact (Hd M HM). }
  assert (G1 : Forall (fun g => veq p (ev p ops g e) []) (J ++ m_products (length ops) G d)).
  { rewrite Forall_forall. intros g Hg. apply in_app_iff in Hg as [Hg|Hg].
    - exact (HJ' g Hg).
    - unfold m_products in Hg. apply in_flat_map in Hg as [k [Hk Hg]].
      apply in_map_iff in Hg as [P [HgP HP]]. subst g.
      destruct (Forall2_In_l _ _ _ _ Hrel HP) as [v [Hv Hr]].
      pose proof (proj1 (in_seq _ _ _) Hk) as Hk'.
      etransitivity; [apply ev_pmul; exact Hpc|].
      etransitivity;
        [apply (lin_proper p _ (ev_lin p ops (var (length ops) k)));
         symmetry; exact Hr|].
      etransitivity; [apply ev_var|].
      etransitivity; [apply mono_unit; lia|].
      apply (HPV v Hv). apply nth_In. lia. }
  intros cs Hlen [u [cofs [Hwu [Hwc [Hlc [Hnz Hz]]]]]].
  set (f := lincomb cs (select_products (length ops) G d sel)) in *.
  assert (H1 : veq p (ev p ops (pmul u f) e) []).
  { etransitivity; [apply pzero_diff; exact Hz|].
    apply ev_combo_zero; [exact Hpc | exact G1]. }
  assert (H2 : veq p (ev p ops f e) []).
  { apply (ev_inj p lev ops Hprime Hst u Hwu Hnz).
    etransitivity; [symmetry; apply ev_pmul; exact Hpc|]. exact H1. }
  assert (H3 : veq p (mv p L (ev p ops f e)) (shift 0 cs)).
  { apply (lincomb_left p ops Hpc e L cs (select_products (length ops) G d sel) 0);
      [exact Hlen|].
    intros j Hj. unfold select_products in Hj. rewrite length_map in Hj.
    unfold select_products.
    rewrite (nth_map_in _ sel j _ 0%nat Hj).
    assert (Hq : veq p (nth (nth j sel 0%nat) (pvecs p ops e G d) e)
                       (ev p ops (nth (nth j sel 0%nat) (products (length ops) G d)
                                    (one_poly (length ops))) e)).
    { exact (Forall2_nth_R _ _ _ _ _ Hrel (ev_one p ops (length ops) e) (nth j sel 0%nat)). }
    etransitivity; [apply (lin_proper p _ (mv_lin p L)); symmetry; exact Hq|].
    assert (Hj' : (j < length (map (fun i => nth i (pvecs p ops e G d) e) sel))%nat)
      by (rewrite length_map; exact Hj).
    pose proof (left_ok_sound p L _ 0 Hleft j Hj') as H0.
    rewrite (nth_map_in _ sel j _ 0%nat Hj) in H0.
    exact H0. }
  assert (H4 : veq p cs []).
  { etransitivity; [symmetry; exact H3|]. apply (lin_zero p _ (mv_lin p L)). exact H2. }
  rewrite Forall_forall. intros c0 Hc.
  destruct (In_nth cs c0 0 Hc) as [i [_ Hi]].
  specialize (H4 i). rewrite Hi, nth_nil_Z in H4. exact H4.
Qed.

Lemma products_pvecs_length p n ops e G d :
  length (products n G d) = length (pvecs p ops e G d).
Proof.
  unfold products. rewrite pvecs_msets.
  exact (Forall2_length (msets_rel (fun (_ : poly) (_ : vec) => True) pmul
           (fun g v => ev p ops g v) (one_poly n) e I (fun _ _ _ _ => I) d G)).
Qed.

Lemma check_cert_sel_range p n J G d c :
  check_cert p n J G d c = true ->
  forall i, In i (c_sel c) -> (i < length (products n G d))%nat.
Proof.
  intros H i Hi. unfold check_cert in H. cbv zeta in H.
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ Hsel].
  rewrite forallb_forall in Hsel. specialize (Hsel i Hi).
  apply Nat.ltb_lt in Hsel.
  rewrite (products_pvecs_length p n (c_ops c) (c_e c) G d). exact Hsel.
Qed.

Lemma prime_7 : prime 7.
Proof.
  apply prime_alt. split; [lia|].
  intros n Hn H. destruct H as [k Hk].
  assert (n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6) as Hc by lia.
  destruct Hc as [E | [E | [E | [E | E]]]]; subst n; lia.
Qed.

Theorem toy_independent :
  independent_mod 7 2 (toy_J ++ m_products 2 toy_G 1)
    (select_products 2 toy_G 1 (c_sel toy_cert)).
Proof. exact (cert_independent 7 2 toy_J toy_G 1 toy_cert prime_7 toy_cert_accepted). Qed.
