(** Module certificates for the Hilbert-function cells of a local ring over a prime field.

    A cell fixes a prime p, a number n of variables, a list J of polynomials in n variables (the ideal of the
    ambient variety), a list G of polynomials (the generators of the ideal whose fiber cone is measured) and
    a degree d. The local ring is R = F_p[t_1 .. t_n]_(t) / (J), P_d is the span of the degree-d products of
    the entries of G, and the cell claims that the quotient (P_d + J) / (m P_d + J) of R has a basis of r
    products, where m = (t_1 .. t_n). This file states the claim ([hilbert_cell]) and defines a checkable
    sufficient condition for its independence half ([check_cert]), calibrated on a two-variable cell.

    Convention: [cg p a b] means p divides a - b, so every statement reads modulo p and no hypothesis on p
    enters until the final cancellation of a nonzero constant term, which uses [prime p]. A vector is a list
    of integers; an entry past the end of the list reads as 0 and two vectors are equal ([veq]) when every
    entry is congruent. A sparse matrix is a list of rows, row b a list of pairs (column c, value v) with
    repeated columns allowed; it sends x to the vector whose entry b is the sum of v x_c over row b, reduced
    modulo p ([mv]). A monomial is an exponent vector of length n and a polynomial a list of pairs
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
    product to the i-th unit vector. *)

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
Definition row := list (nat * Z).
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

Fixpoint mv (p : Z) (M : spmat) (x : vec) : vec :=
  match M with
  | [] => []
  | r :: M' => (ksum r (fun c => nth c x 0) mod p) :: mv p M' x
  end.

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
  nth b (mv p M x) 0 = ksum (nth b M []) (fun c => nth c x 0) mod p.
Proof.
  revert b. induction M as [|r M IH]; intros b.
  - destruct b; reflexivity.
  - destruct b as [|b]; simpl; [reflexivity | apply IH].
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
  cg p (nth b (mv p M x) 0) (ksum (nth b M []) (fun c => nth c x 0)).
Proof. rewrite nth_mv. apply cg_mod. Qed.

Lemma mv_lin p M : lin p (mv p M).
Proof.
  split; [|split].
  - intros x y H b.
    eapply cg_trans; [apply mv_nth_cg|].
    eapply cg_trans; [|apply cg_sym; apply mv_nth_cg].
    apply ksum_cg. intros c. apply H.
  - intros x y b.
    eapply cg_trans; [apply mv_nth_cg|].
    eapply cg_trans; [|apply cg_sym; apply nth_vadd].
    eapply cg_trans.
    + apply ksum_cg with (G := fun c => nth c x 0 + nth c y 0). intros c. apply nth_vadd.
    + eapply cg_trans;
        [apply cg_eq; exact (ksum_add_fun (nth b M []) (fun c => nth c x 0) (fun c => nth c y 0))|].
      apply cg_add; apply cg_sym; apply mv_nth_cg.
  - intros c x b.
    eapply cg_trans; [apply mv_nth_cg|].
    eapply cg_trans; [|apply cg_sym; apply nth_vscale].
    eapply cg_trans.
    + apply ksum_cg with (G := fun c' => c * nth c' x 0). intros c'. apply nth_vscale.
    + eapply cg_trans;
        [apply cg_eq; exact (ksum_scale_fun (nth b M []) c (fun c' => nth c' x 0))|].
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
  flat_map (fun cv => map (fun t => (fst t, snd cv * snd t)) (nth (fst cv) N [])) (nth b M []).

Definition rowdiff_b (p : Z) (R1 R2 : row) : bool :=
  let L := R1 ++ map (fun t => (fst t, - snd t)) R2 in
  forallb (fun c => Z.eqb (kcoef Nat.eq_dec L c mod p) 0) (map fst L).

Definition comm_b (p : Z) (M N : spmat) : bool :=
  forallb (fun b => rowdiff_b p (rowprod M N b) (rowprod N M b))
    (seq 0 (Nat.max (length M) (length N))).

Definition strict_b (p : Z) (lev : list nat) (M : spmat) : bool :=
  forallb (fun b => forallb (fun cv => Z.eqb (snd cv mod p) 0 ||
                                 Nat.ltb (nth (fst cv) lev 0%nat) (nth b lev 0%nat))
                      (nth b M []))
    (seq 0 (length M)).

Fixpoint left_ok (p : Z) (L : spmat) (vs : list vec) (i : nat) : bool :=
  match vs with
  | [] => true
  | v :: vs' => vzero_b p (vadd p (mv p L v) (vscale p (-1) (shift i [1]))) &&
                left_ok p L vs' (S i)
  end.

Definition pv_list (p : Z) (n : nat) (ops : list spmat) (e : vec) (G : list poly) (d : nat)
  : list (poly * vec) :=
  msets (fun g pv => (pmul g (fst pv), ev p ops g (snd pv))) (one_poly n, e) d G.

Record cert := mk_cert {
  c_ops : list spmat;
  c_lev : list nat;
  c_e : vec;
  c_left : spmat;
  c_sel : list nat }.

Definition check_cert (p : Z) (n : nat) (J G : list poly) (d : nat) (c : cert) : bool :=
  let ops := c_ops c in
  let PV := pv_list p n ops (c_e c) G d in
  Nat.eqb (length ops) n
  && forallb (fun M => forallb (fun N => comm_b p M N) ops) ops
  && forallb (strict_b p (c_lev c)) ops
  && forallb (fun g => vzero_b p (ev p ops g (c_e c))) J
  && forallb (fun pv => forallb (fun M => vzero_b p (mv p M (snd pv))) ops) PV
  && forallb (fun i => Nat.ltb i (length PV)) (c_sel c)
  && left_ok p (c_left c) (map (fun i => snd (nth i PV (one_poly n, c_e c))) (c_sel c)) 0.

(** * Calibration: a two-variable cell over F_7 *)

Definition toy_J : list poly := [ [([2%nat; 0%nat], 1)]; [([0%nat; 2%nat], 1)] ].
Definition toy_G : list poly := [ [([1%nat; 0%nat], 1)]; [([0%nat; 1%nat], 3)] ].

Definition toy_cert : cert :=
  mk_cert
    [ [ []; [(0%nat, 1)]; [] ]; [ []; []; [(0%nat, 1)] ] ]
    [0%nat; 1%nat; 1%nat]
    [1; 0; 0]
    [ [(1%nat, 1)]; [(2%nat, 5)] ]
    [0%nat; 1%nat].

Lemma toy_cert_accepted : check_cert 7 2 toy_J toy_G 1 toy_cert = true.
Proof. vm_compute. reflexivity. Qed.

Definition toy_left_mutant : cert :=
  mk_cert (c_ops toy_cert) (c_lev toy_cert) (c_e toy_cert)
    [ [(1%nat, 1)]; [(2%nat, 4)] ] (c_sel toy_cert).

Lemma toy_left_mutant_rejected : check_cert 7 2 toy_J toy_G 1 toy_left_mutant = false.
Proof. vm_compute. reflexivity. Qed.

Definition toy_comm_mutant : cert :=
  mk_cert [ [ []; [(0%nat, 1)]; [] ]; [ []; [(0%nat, 1)]; [(0%nat, 1)] ] ]
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
