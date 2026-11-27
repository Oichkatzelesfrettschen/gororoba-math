(** Upper bound for the Hilbert cells of a quadric ideal: from membership of the quadrics to spanning of the products.

    A cell of HilbertCellCertificate.v fixes a prime p, n variables t, a list J of polynomials in t, a list G of
    generators and a degree d. Its upper bound is the statement [spans_mod]: every degree-d product of G is a
    combination of the selected products modulo the local ideal J + m (G)^d. This file derives that statement
    from two certificates. K2CofactorCertificate.v certifies, for each quadric q of the variables y_a (one per
    generator), that q(G) lies in the local ideal of J + m (G)^2. A reduction certificate lists, for each
    monomial of degree d in y that is not standard, an identity in F_p[y]: the monomial equals a combination of
    standard monomials plus a combination of multiples y^m q_i of the quadrics, the multipliers y^m having
    degree d - 2. Substituting G for y turns the identity into a congruence of products, and the multiples
    y^m q_i(G) lie in J + m (G)^d because a product of d - 2 generators times J + m (G)^2 lies in J + m (G)^d.

    Convention: polynomials, monomials, [cg], [pcoef] and [products] are those of HilbertCellCertificate.v. A
    monomial y^e of the variables y_1 .. y_k (k the length of G) is the exponent list e of length k and
    [ymono n G e] is its image under y_a -> G_a. [ksum f F] is the sum of the coefficients of f times F of the
    monomials; two polynomials are [se] (equal for every F) when they agree as formal sums, which the ring laws
    of [pmul] satisfy exactly over the integers, and [Idl] and [LI] are the ideal and local-ideal membership
    predicates restated through [ksum] (equivalent to [in_local_ideal], see [LI_of_ili] and [ili_of_LI]). Every
    congruence is modulo p and the unit of a local-ideal certificate is multiplied through [prime p].

    Reduction certificate format: a list of [red_entry], one for each non-standard monomial of degree d in y.
    The entry (mu, mult, std) stands for the identity y^mu = sum_{(i,m,a) in mult} a y^m q_i + sum_{(s,c) in std}
    c y^s over F_p; q_i is the i-th quadric (a list of (coefficient, exponent list)), m an exponent list of
    length k and sum d - 2, and each s a standard monomial. The standard monomials S are a duplicate-free list
    of exponent lists of length k and sum d. [check_entry] also requires the exponent sum of mu to be d and each
    quadric index to be below the number of quadrics; these checks fix the format and the proofs do not use them.

    The checker splits in two. [check_red] checks the reduction data alone: the degree, the generators, the
    quadrics as data, S, every entry and the coverage of all monomials of degree d. The membership of each quadric
    in the local ideal of J + m (G)^2 is a hypothesis of the [_of_red] theorems, [forall q, In q Q -> LI p n
    (J ++ m_products n G 2) (subst_q n G q)], the form [entry_sound] consumes; any certificate that proves it for
    one quadric at a time supplies it (the cofactor checker of K2CofactorCertificate.v, a factored or
    basis-changed route, a chunked check). [check_bound] is [check_red] together with the unfactored cofactor
    certificate of every quadric, and its theorems are corollaries of the [_of_red] ones through
    [check_bound_red] and [check_bound_members].

    Main results: [hilbert_upper_bound_of_red] (the spanning statement
    [spans_mod p n (J ++ m_products n G d) (products n G d) (map (ymono n G) S)] from [check_red] and the
    membership hypothesis), [hilbert_upper_sel_of_red] (the statement for products selected by index),
    [hilbert_cell_of_red] (the cell statement from an independent selection aligned with S); the monolithic
    corollaries [hilbert_upper_bound], [hilbert_upper_sel] and [hilbert_cell_of_bound] from [check_bound]; and the
    toy calibration [toy_bound_accepted] with five [_rejected] lemmas. *)

From Stdlib Require Import ZArith Lia List Bool PeanoNat NArith Znumtheory Setoid Morphisms.
Require Import HilbertCellCertificate K2CofactorCertificate.
Import ListNotations.
Open Scope Z_scope.

(** * Exponent sums and lengths *)

Fixpoint msum (m : mono) : nat :=
  match m with
  | [] => 0%nat
  | x :: m' => (x + msum m')%nat
  end.

Lemma madd_comm a : forall b, madd a b = madd b a.
Proof.
  induction a as [|x a IH]; intros [|y b]; try reflexivity.
  cbn [madd]. rewrite IH, Nat.add_comm; try reflexivity.
Qed.

Lemma madd_assoc a : forall b c, madd (madd a b) c = madd a (madd b c).
Proof.
  induction a as [|x a IH]; intros b c.
  - reflexivity.
  - destruct b as [|y b]; [reflexivity|].
    destruct c as [|z c]; [reflexivity|].
    cbn [madd]. rewrite IH, Nat.add_assoc; try reflexivity.
Qed.

Lemma msum_madd a : forall b, msum (madd a b) = (msum a + msum b)%nat.
Proof.
  induction a as [|x a IH]; intros [|y b].
  - reflexivity.
  - reflexivity.
  - cbn [madd msum]. lia.
  - cbn [madd msum]. rewrite IH. lia.
Qed.

Lemma length_madd a : forall b, length a = length b -> length (madd a b) = length a.
Proof.
  induction a as [|x a IH]; intros [|y b] H; try discriminate H; [reflexivity|].
  cbn [madd length]. f_equal. apply IH. cbn [length] in H. lia.
Qed.

Lemma madd_zero_l n : forall b, length b = n -> madd (repeat 0%nat n) b = b.
Proof.
  induction n as [|n IH]; intros [|y b] H; cbn [length] in H; try discriminate H; [reflexivity|].
  cbn [repeat madd]. f_equal. apply IH. lia.
Qed.

Lemma wf_nil n : wf_poly n [].
Proof. unfold wf_poly. constructor. Qed.

Lemma wf_one n : wf_poly n (one_poly n).
Proof. unfold wf_poly, one_poly. constructor; [cbn [fst]; apply repeat_length | constructor]. Qed.

Lemma length_unit_mono n : forall k, length (unit_mono n k) = n.
Proof.
  induction n as [|n IH]; intros k.
  - destruct k; reflexivity.
  - destruct k as [|k]; cbn [unit_mono length]; f_equal.
    + apply repeat_length.
    + apply IH.
Qed.

Lemma wf_var n k : wf_poly n (var n k).
Proof. unfold wf_poly, var. constructor; [cbn [fst]; apply length_unit_mono | constructor]. Qed.

Lemma wf_pmul n f g : wf_poly n f -> wf_poly n g -> wf_poly n (pmul f g).
Proof.
  unfold wf_poly. intros Hf Hg. apply Forall_forall. intros t Ht.
  unfold pmul in Ht. apply in_flat_map in Ht as [s [Hs Ht]].
  apply in_map_iff in Ht as [t' [<- Ht']].
  rewrite Forall_forall in Hf, Hg.
  pose proof (Hf s Hs) as E1. pose proof (Hg t' Ht') as E2. cbv beta in E1, E2.
  cbn [fst]. rewrite (length_madd (fst s) (fst t') (eq_trans E1 (eq_sym E2))). exact E1.
Qed.

Lemma wf_app n x y : wf_poly n x -> wf_poly n y -> wf_poly n (x ++ y).
Proof. unfold wf_poly. intros Hx Hy. apply Forall_app. split; assumption. Qed.

Lemma forall_repeat_nil n k : Forall (wf_poly n) (repeat [] k).
Proof. induction k as [|k IH]; [constructor|]. cbn [repeat]. constructor; [apply wf_nil | exact IH]. Qed.

Lemma wf_pow n g k : wf_poly n g -> wf_poly n (pow_poly n g k).
Proof.
  intros Hg. induction k as [|k IH]; cbn [pow_poly]; [apply wf_one | apply wf_pmul; assumption].
Qed.

Lemma wf_ymono n G : Forall (wf_poly n) G -> forall e, wf_poly n (ymono n G e).
Proof.
  intros HG. induction G as [|g G IH]; intros e.
  - destruct e; apply wf_one.
  - destruct e as [|k e]; [apply wf_one|].
    cbn [ymono]. apply wf_pmul.
    + apply wf_pow. exact (Forall_inv HG).
    + apply IH. exact (Forall_inv_tail HG).
Qed.

Lemma products_0 n G : products n G 0 = [one_poly n].
Proof. reflexivity. Qed.

Lemma products_nil_S n d : products n [] (S d) = [].
Proof. reflexivity. Qed.

Lemma products_cons_S n g G d :
  products n (g :: G) (S d) = map (pmul g) (products n (g :: G) d) ++ products n G (S d).
Proof. reflexivity. Qed.

Lemma wf_products n G : Forall (wf_poly n) G -> forall d rho, In rho (products n G d) -> wf_poly n rho.
Proof.
  intros HG. induction G as [|g G IH]; intros d; induction d as [|d IHd]; intros rho Hin.
  - rewrite products_0 in Hin. destruct Hin as [<-|[]]. apply wf_one.
  - rewrite products_nil_S in Hin. destruct Hin.
  - rewrite products_0 in Hin. destruct Hin as [<-|[]]. apply wf_one.
  - rewrite products_cons_S in Hin. apply in_app_iff in Hin as [Hin|Hin].
    + apply in_map_iff in Hin as [rho' [<- Hin]].
      apply wf_pmul; [exact (Forall_inv HG) | apply IHd; exact Hin].
    + exact (IH (Forall_inv_tail HG) (S d) rho Hin).
Qed.

(** * Sums over polynomials *)

Lemma ksum_cons (t : mono * Z) (l : poly) F : ksum (t :: l) F = snd t * F (fst t) + ksum l F.
Proof. reflexivity. Qed.

Lemma ksum_nil (F : mono -> Z) : ksum ([] : poly) F = 0.
Proof. reflexivity. Qed.

Lemma ksum_single (m : mono) (c : Z) F : ksum [(m, c)] F = c * F m.
Proof. cbn [ksum fst snd]. ring. Qed.

Lemma ksum_ext (l : poly) (F G : mono -> Z) : (forall k, F k = G k) -> ksum l F = ksum l G.
Proof.
  intros H. induction l as [|t l IH]; [reflexivity|].
  rewrite !ksum_cons, H, IH; try reflexivity.
Qed.

Lemma ksum_ext_in (l : poly) (F G : mono -> Z) :
  (forall t, In t l -> F (fst t) = G (fst t)) -> ksum l F = ksum l G.
Proof.
  intros H. induction l as [|t l IH]; [reflexivity|].
  rewrite !ksum_cons. rewrite (H t (or_introl eq_refl)).
  rewrite (IH (fun t' Ht' => H t' (or_intror Ht'))); try reflexivity.
Qed.

Lemma ksum_zero_fun (l : poly) : ksum l (fun _ => 0) = 0.
Proof. induction l as [|t l IH]; [reflexivity|]. rewrite ksum_cons, IH. ring. Qed.

Lemma ksum_swap (f g : poly) (H : mono -> mono -> Z) :
  ksum f (fun a => ksum g (fun b => H a b)) = ksum g (fun b => ksum f (fun a => H a b)).
Proof.
  induction f as [|s f IH].
  - cbn [ksum]. symmetry. apply ksum_zero_fun.
  - rewrite ksum_cons.
    assert (E : forall b, ksum (s :: f) (fun a => H a b) = snd s * H (fst s) b + ksum f (fun a => H a b))
      by (intros b; reflexivity).
    rewrite (ksum_ext g (fun b => ksum (s :: f) (fun a => H a b))
      (fun b => snd s * H (fst s) b + ksum f (fun a => H a b)) E).
    rewrite ksum_add_fun, ksum_scale_fun, IH. reflexivity.
Qed.

Lemma ksum_map_pair (g : poly) (a : mono) (c : Z) F :
  ksum (map (fun t => (madd a (fst t), c * snd t)) g) F = c * ksum g (fun b => F (madd a b)).
Proof.
  induction g as [|t g IH]; [cbn [map ksum]; ring|].
  cbn [map]. rewrite !ksum_cons, IH. cbn [fst snd]. ring.
Qed.

Lemma ksum_pmul (f g : poly) F :
  ksum (pmul f g) F = ksum f (fun a => ksum g (fun b => F (madd a b))).
Proof.
  induction f as [|s f IH]; [reflexivity|].
  change (pmul (s :: f) g) with (map (fun t => (madd (fst s) (fst t), snd s * snd t)) g ++ pmul f g).
  rewrite ksum_app, IH, ksum_map_pair, ksum_cons. reflexivity.
Qed.

Lemma ksum_delta (l : poly) m :
  ksum l (fun k => if mono_eq_dec k m then 1 else 0) = pcoef l m.
Proof.
  induction l as [|t l IH]; [reflexivity|].
  rewrite ksum_cons, IH, pcoef_cons. cbv beta.
  destruct (mono_eq_dec (fst t) m); ring.
Qed.

(** * Formal equality of polynomials *)

Definition se (f g : poly) : Prop := forall F : mono -> Z, ksum f F = ksum g F.

#[export] Instance se_Equiv : Equivalence se.
Proof.
  constructor.
  - intros f F. reflexivity.
  - intros f g H F. symmetry. exact (H F).
  - intros f g h H1 H2 F. rewrite (H1 F). exact (H2 F).
Qed.

#[export] Instance pmul_se : Proper (se ==> se ==> se) pmul.
Proof.
  intros f f' Hf g g' Hg F.
  rewrite !ksum_pmul.
  rewrite (ksum_ext f (fun a => ksum g (fun b => F (madd a b)))
    (fun a => ksum g' (fun b => F (madd a b))) (fun a => Hg (fun b => F (madd a b)))).
  apply Hf.
Qed.

#[export] Instance app_se : Proper (se ==> se ==> se) (@app (mono * Z)).
Proof.
  intros f f' Hf g g' Hg F.
  rewrite !ksum_app, (Hf F), (Hg F); try reflexivity.
Qed.

Lemma se_pmul_comm f g : se (pmul f g) (pmul g f).
Proof.
  intros F. rewrite !ksum_pmul.
  pose proof (ksum_swap f g (fun a b => F (madd a b))) as E. cbv beta in E.
  rewrite E. apply ksum_ext. intros b. apply ksum_ext. intros a.
  rewrite madd_comm; try reflexivity.
Qed.

Lemma se_pmul_assoc f g h : se (pmul (pmul f g) h) (pmul f (pmul g h)).
Proof.
  intros F.
  rewrite (ksum_pmul (pmul f g) h F).
  rewrite (ksum_pmul f g (fun x => ksum h (fun c => F (madd x c)))).
  rewrite (ksum_pmul f (pmul g h) F).
  apply ksum_ext. intros a. cbv beta.
  rewrite (ksum_pmul g h (fun y => F (madd a y))).
  apply ksum_ext. intros b. apply ksum_ext. intros c.
  rewrite madd_assoc; try reflexivity.
Qed.

Lemma pmul_app_l f f' g : pmul (f ++ f') g = pmul f g ++ pmul f' g.
Proof. unfold pmul. apply flat_map_app. Qed.

Lemma se_pmul_app_r f g g' : se (pmul f (g ++ g')) (pmul f g ++ pmul f g').
Proof.
  intros F. rewrite ksum_app. rewrite !ksum_pmul.
  rewrite <- ksum_add_fun.
  apply ksum_ext. intros a. apply ksum_app.
Qed.

Lemma se_pmul_nil_r f : se (pmul f []) [].
Proof.
  intros F. rewrite ksum_pmul.
  assert (E : forall a, ksum ([] : poly) (fun b => F (madd a b)) = 0) by (intros a; reflexivity).
  rewrite (ksum_ext f _ (fun _ => 0) E), ksum_zero_fun. reflexivity.
Qed.

Lemma se_pmul_one_l n f : wf_poly n f -> se (pmul (one_poly n) f) f.
Proof.
  intros Hf F. rewrite ksum_pmul. unfold one_poly.
  rewrite ksum_single.
  rewrite Z.mul_1_l.
  apply ksum_ext_in. intros t Ht. cbv beta.
  assert (Hl : length (fst t) = n) by (unfold wf_poly in Hf; rewrite Forall_forall in Hf; exact (Hf t Ht)).
  rewrite (madd_zero_l n (fst t) Hl); try reflexivity.
Qed.

Definition kb_scale (a : Z) (f : poly) : poly := map (fun t => (fst t, a * snd t)) f.

Lemma ksum_kb_scale a f F : ksum (kb_scale a f) F = a * ksum f F.
Proof. unfold kb_scale. apply ksum_scale_list. Qed.

Lemma se_pmul_scale_l a f g : se (pmul (kb_scale a f) g) (kb_scale a (pmul f g)).
Proof.
  intros F. rewrite ksum_kb_scale, !ksum_pmul, ksum_kb_scale; try reflexivity.
Qed.

Lemma se_pmul_scale_r a f g : se (pmul f (kb_scale a g)) (kb_scale a (pmul f g)).
Proof.
  intros F. rewrite ksum_kb_scale, !ksum_pmul.
  assert (E : forall x, ksum (kb_scale a g) (fun b => F (madd x b)) = a * ksum g (fun b => F (madd x b)))
    by (intros x; apply ksum_kb_scale).
  rewrite (ksum_ext f _ _ E), ksum_scale_fun; try reflexivity.
Qed.

Lemma wf_kb_scale n a f : wf_poly n f -> wf_poly n (kb_scale a f).
Proof.
  unfold wf_poly, kb_scale. intros H. apply Forall_forall. intros t Ht.
  apply in_map_iff in Ht as [t' [<- Ht']]. cbn [fst].
  rewrite Forall_forall in H. exact (H t' Ht').
Qed.

Lemma se_pmul_4 A B C D : se (pmul (pmul A B) (pmul C D)) (pmul (pmul A C) (pmul B D)).
Proof.
  rewrite (se_pmul_assoc A B (pmul C D)).
  rewrite (se_pmul_assoc A C (pmul B D)).
  refine (pmul_se A A (reflexivity A) _ _ _).
  rewrite <- (se_pmul_assoc B C D), (se_pmul_comm B C), (se_pmul_assoc C B D).
  reflexivity.
Qed.

(** * Congruence of sums modulo p *)

Lemma pe_pzero p a b :
  (forall F, cg p (ksum a F) (ksum b F)) <-> pzero p (padd a (pneg b)).
Proof.
  split.
  - intros H m.
    pose proof (H (fun k => if mono_eq_dec k m then 1 else 0)) as H1.
    rewrite !ksum_delta in H1.
    unfold padd. rewrite pcoef_app, pcoef_pneg.
    unfold cg in *.
    replace (pcoef a m + - pcoef b m - 0) with (pcoef a m - pcoef b m) by ring.
    exact H1.
  - intros H F.
    pose proof (ksum_zero_keys mono_eq_dec p (padd a (pneg b)) F (fun k _ => H k)) as H1.
    unfold padd in H1. rewrite ksum_app in H1.
    unfold pneg in H1. rewrite ksum_neg_list in H1.
    unfold cg in *.
    replace (ksum a F - ksum b F) with (ksum a F + - ksum b F - 0) by ring.
    exact H1.
Qed.

Lemma cg_rearr p A B C : cg p (1 * A) (B + C) -> cg p (A + - C) B.
Proof.
  unfold cg. intros H.
  replace (A + - C - B) with (1 * A - (B + C)) by ring. exact H.
Qed.

(** * Ideal membership through sums *)

Fixpoint csum (cs gs : list poly) (F : mono -> Z) : Z :=
  match cs, gs with
  | c :: cs', g :: gs' => ksum (pmul c g) F + csum cs' gs' F
  | _, _ => 0
  end.

Lemma ksum_combo cs gs F : ksum (combo cs gs) F = csum cs gs F.
Proof.
  revert gs. induction cs as [|c cs IH]; intros gs; [destruct gs; reflexivity|].
  destruct gs as [|g gs]; [reflexivity|].
  cbn [combo csum]. rewrite ksum_app, IH; try reflexivity.
Qed.

Definition Idl (p : Z) (n : nat) (gens : list poly) (f : poly) : Prop :=
  exists cofs, Forall (wf_poly n) cofs /\ length cofs = length gens /\
    forall F, cg p (ksum f F) (csum cofs gens F).

Definition LI (p : Z) (n : nat) (gens : list poly) (f : poly) : Prop :=
  exists u, wf_poly n u /\ ~ cg p (const_coef u) 0 /\ Idl p n gens (pmul u f).

Lemma LI_of_ili p n gens f : in_local_ideal p n gens f -> LI p n gens f.
Proof.
  intros [u [cofs [Hu [Hc [Hl [Hn Hz]]]]]].
  exists u. split; [exact Hu|]. split; [exact Hn|].
  exists cofs. split; [exact Hc|]. split; [exact Hl|].
  intros F. rewrite <- ksum_combo.
  exact (proj2 (pe_pzero p _ _) Hz F).
Qed.

Lemma ili_of_LI p n gens f : LI p n gens f -> in_local_ideal p n gens f.
Proof.
  intros [u [Hu [Hn [cofs [Hc [Hl H]]]]]].
  exists u, cofs. refine (conj Hu (conj Hc (conj Hl (conj Hn _)))).
  apply (proj1 (pe_pzero p _ _)). intros F. rewrite ksum_combo. exact (H F).
Qed.

Lemma Idl_pe p n gens f f' :
  (forall F, cg p (ksum f F) (ksum f' F)) -> Idl p n gens f' -> Idl p n gens f.
Proof.
  intros H [cofs [Hc [Hl H2]]]. exists cofs. refine (conj Hc (conj Hl _)).
  intros F. exact (cg_trans p _ _ _ (H F) (H2 F)).
Qed.

Lemma Idl_se p n gens f f' : se f f' -> Idl p n gens f' -> Idl p n gens f.
Proof.
  intros H. apply Idl_pe. intros F. rewrite (H F). apply cg_refl.
Qed.

Lemma csum_nils gens : forall k F, csum (repeat [] k) gens F = 0.
Proof.
  induction gens as [|g gens IH]; intros [|k] F; try reflexivity.
  cbn [repeat csum]. rewrite IH. reflexivity.
Qed.

Lemma Idl_nil p n gens : Idl p n gens [].
Proof.
  exists (repeat [] (length gens)). split; [apply forall_repeat_nil|].
  split; [apply repeat_length|].
  intros F. rewrite ksum_nil, csum_nils. apply cg_refl.
Qed.

Fixpoint zipc (a b : list poly) : list poly :=
  match a, b with
  | x :: a', y :: b' => (x ++ y) :: zipc a' b'
  | _, _ => []
  end.

Lemma wf_zipc n : forall a b, Forall (wf_poly n) a -> Forall (wf_poly n) b -> Forall (wf_poly n) (zipc a b).
Proof.
  induction a as [|x a IH]; intros b Ha Hb.
  - constructor.
  - destruct b as [|y b]; [constructor|].
    cbn [zipc]. constructor.
    + apply wf_app; [exact (Forall_inv Ha) | exact (Forall_inv Hb)].
    + apply IH; [exact (Forall_inv_tail Ha) | exact (Forall_inv_tail Hb)].
Qed.

Lemma length_zipc : forall a b, length a = length b -> length (zipc a b) = length a.
Proof.
  induction a as [|x a IH]; intros [|y b] H; try discriminate H; [reflexivity|].
  cbn [zipc length]. f_equal. apply IH. cbn [length] in H. lia.
Qed.

Lemma csum_zipc gens : forall a b F, length a = length gens -> length b = length gens ->
  csum (zipc a b) gens F = csum a gens F + csum b gens F.
Proof.
  induction gens as [|g gens IH]; intros [|x a] [|y b] F Ha Hb; cbn [length] in Ha, Hb;
    try discriminate Ha; try discriminate Hb; try reflexivity.
  cbn [zipc csum]. rewrite (IH a b F) by lia.
  rewrite pmul_app_l, ksum_app. ring.
Qed.

Lemma Idl_add p n gens f f' : Idl p n gens f -> Idl p n gens f' -> Idl p n gens (f ++ f').
Proof.
  intros [a [Ha [La Ea]]] [b [Hb [Lb Eb]]].
  exists (zipc a b). split; [apply wf_zipc; assumption|].
  split; [rewrite (length_zipc a b (eq_trans La (eq_sym Lb))); exact La|].
  intros F. rewrite ksum_app, (csum_zipc gens a b F La Lb).
  apply cg_add; [apply Ea | apply Eb].
Qed.

Lemma csum_map_pmul h : forall cs gens F,
  csum (map (pmul h) cs) gens F = ksum h (fun a => csum cs gens (fun b => F (madd a b))).
Proof.
  induction cs as [|c cs IH]; intros [|g gens] F.
  - cbn [map csum]. symmetry. apply ksum_zero_fun.
  - cbn [map csum]. symmetry. apply ksum_zero_fun.
  - cbn [map csum]. symmetry. apply ksum_zero_fun.
  - cbn [map csum]. rewrite IH, ksum_add_fun.
    rewrite (se_pmul_assoc h c g F), ksum_pmul; try reflexivity.
Qed.

Lemma Idl_scalep p n gens h f : wf_poly n h -> Idl p n gens f -> Idl p n gens (pmul h f).
Proof.
  intros Hh [cofs [Hc [Hl H]]].
  exists (map (pmul h) cofs).
  split.
  { apply Forall_forall. intros x Hx. apply in_map_iff in Hx as [c [<- Hc']].
    apply wf_pmul; [exact Hh | rewrite Forall_forall in Hc; exact (Hc c Hc')]. }
  split; [rewrite length_map; exact Hl|].
  intros F. rewrite csum_map_pmul, ksum_pmul.
  apply ksum_cg. intros a. apply H.
Qed.

Lemma csum_map_scale a : forall cs gens F,
  csum (map (kb_scale a) cs) gens F = a * csum cs gens F.
Proof.
  induction cs as [|c cs IH]; intros [|g gens] F.
  - cbn [map csum]. ring.
  - cbn [map csum]. ring.
  - cbn [map csum]. ring.
  - cbn [map csum]. rewrite IH, (se_pmul_scale_l a c g F), ksum_kb_scale. ring.
Qed.

Lemma Idl_scalec p n gens a f : Idl p n gens f -> Idl p n gens (kb_scale a f).
Proof.
  intros [cofs [Hc [Hl H]]].
  exists (map (kb_scale a) cofs). split.
  { apply Forall_forall. intros x Hx. apply in_map_iff in Hx as [c [<- Hc']].
    apply wf_kb_scale. rewrite Forall_forall in Hc. exact (Hc c Hc'). }
  split; [rewrite length_map; exact Hl|].
  intros F. rewrite ksum_kb_scale, csum_map_scale.
  apply cg_mul; [apply cg_refl | apply H].
Qed.

Lemma Idl_mem p n gens g h : In g gens -> wf_poly n h -> Idl p n gens (pmul h g).
Proof.
  intros Hin Hh. induction gens as [|g0 gens IH]; [destruct Hin|].
  destruct Hin as [E|Hin].
  - subst g0. exists (h :: repeat [] (length gens)). split.
    + constructor; [exact Hh | apply forall_repeat_nil].
    + split; [cbn [length]; f_equal; apply repeat_length|].
      intros F. cbn [csum]. rewrite csum_nils, Z.add_0_r. apply cg_refl.
  - destruct (IH Hin) as [cofs [Hc [Hl H]]].
    exists ([] :: cofs). split; [constructor; [apply wf_nil | exact Hc]|].
    split; [cbn [length]; f_equal; exact Hl|].
    intros F. specialize (H F). cbn [csum].
    change (ksum (pmul [] g0) F) with 0. rewrite Z.add_0_l. exact H.
Qed.

Lemma Idl_memw p n gens g : In g gens -> wf_poly n g -> Idl p n gens g.
Proof.
  intros Hin Hg. apply (Idl_se p n gens g (pmul (one_poly n) g)).
  - symmetry. apply se_pmul_one_l. exact Hg.
  - apply Idl_mem; [exact Hin | apply wf_one].
Qed.

Lemma Idl_combo_pi p n gens pi : wf_poly n pi ->
  forall cs gs, Forall (wf_poly n) cs -> (forall g, In g gs -> Idl p n gens (pmul pi g)) ->
  Idl p n gens (pmul pi (combo cs gs)).
Proof.
  intros Hpi. induction cs as [|c cs IH]; intros gs Hc Hg.
  - apply (Idl_se p n gens _ []); [apply se_pmul_nil_r | apply Idl_nil].
  - destruct gs as [|g gs].
    + apply (Idl_se p n gens _ []); [apply se_pmul_nil_r | apply Idl_nil].
    + cbn [combo].
      apply (Idl_se p n gens _ (pmul pi (pmul c g) ++ pmul pi (combo cs gs))).
      * apply se_pmul_app_r.
      * apply Idl_add.
        -- apply (Idl_se p n gens _ (pmul c (pmul pi g))).
           ++ rewrite <- (se_pmul_assoc pi c g), (se_pmul_comm pi c), (se_pmul_assoc c pi g). reflexivity.
           ++ apply Idl_scalep; [exact (Forall_inv Hc) | apply Hg; left; reflexivity].
        -- apply IH; [exact (Forall_inv_tail Hc) | intros g' Hg'; apply Hg; right; exact Hg'].
Qed.

Lemma Idl_gens_change p n gens2 gensd pi : wf_poly n pi ->
  (forall g, In g gens2 -> Idl p n gensd (pmul pi g)) ->
  forall f, Idl p n gens2 f -> Idl p n gensd (pmul pi f).
Proof.
  intros Hpi Hg f [cofs [Hc [Hl H]]].
  apply (Idl_pe p n gensd (pmul pi f) (pmul pi (combo cofs gens2))).
  - intros F. rewrite !ksum_pmul. apply ksum_cg. intros a. cbv beta.
    rewrite ksum_combo. apply H.
  - apply Idl_combo_pi; assumption.
Qed.

(** * Local ideal membership with a unit *)

Lemma forallb_repeat_zero n : forallb (Nat.eqb 0%nat) (repeat 0%nat n) = true.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [repeat forallb]. exact IH. Qed.

Lemma one_unit p n : prime p -> ~ cg p (const_coef (one_poly n)) 0.
Proof.
  intros Hp.
  assert (E : const_coef (one_poly n) = 1).
  { unfold one_poly. cbn [const_coef fst snd]. rewrite forallb_repeat_zero; try reflexivity. }
  rewrite E. intros H. unfold cg in H. rewrite Z.sub_0_r in H.
  destruct Hp as [Hp1 _].
  pose proof (Z.divide_pos_le p 1 ltac:(lia) H). lia.
Qed.

Lemma LI_nil p n gens : prime p -> LI p n gens [].
Proof.
  intros Hp. exists (one_poly n). split; [apply wf_one|]. split; [apply one_unit; exact Hp|].
  apply (Idl_se p n gens _ []); [apply se_pmul_nil_r | apply Idl_nil].
Qed.

Lemma LI_pe p n gens f f' :
  (forall F, cg p (ksum f F) (ksum f' F)) -> LI p n gens f' -> LI p n gens f.
Proof.
  intros H [u [Hu [Hn HI]]]. exists u. split; [exact Hu|]. split; [exact Hn|].
  apply (Idl_pe p n gens (pmul u f) (pmul u f')); [|exact HI].
  intros F. rewrite !ksum_pmul. apply ksum_cg. intros a. apply H.
Qed.

Lemma LI_scalec p n gens a f : LI p n gens f -> LI p n gens (kb_scale a f).
Proof.
  intros [u [Hu [Hn HI]]]. exists u. split; [exact Hu|]. split; [exact Hn|].
  apply (Idl_se p n gens _ (kb_scale a (pmul u f))); [apply se_pmul_scale_r | apply Idl_scalec; exact HI].
Qed.

Lemma const_coef_app f g : const_coef (f ++ g) = const_coef f + const_coef g.
Proof. induction f as [|t f IH]; [reflexivity|]. cbn [app const_coef]. rewrite IH. ring. Qed.

Lemma zmono_madd a : forall b,
  forallb (Nat.eqb 0%nat) (madd a b) = (forallb (Nat.eqb 0%nat) a && forallb (Nat.eqb 0%nat) b)%bool.
Proof.
  induction a as [|x a IH]; intros [|y b].
  - reflexivity.
  - reflexivity.
  - change (madd (x :: a) []) with (x :: a).
    change (forallb (Nat.eqb 0%nat) []) with true.
    symmetry. apply andb_true_r.
  - change (madd (x :: a) (y :: b)) with ((x + y)%nat :: madd a b).
    change (forallb (Nat.eqb 0%nat) ((x + y)%nat :: madd a b))
      with (Nat.eqb 0%nat (x + y)%nat && forallb (Nat.eqb 0%nat) (madd a b))%bool.
    change (forallb (Nat.eqb 0%nat) (x :: a)) with (Nat.eqb 0%nat x && forallb (Nat.eqb 0%nat) a)%bool.
    change (forallb (Nat.eqb 0%nat) (y :: b)) with (Nat.eqb 0%nat y && forallb (Nat.eqb 0%nat) b)%bool.
    rewrite IH.
    destruct (forallb (Nat.eqb 0%nat) a), (forallb (Nat.eqb 0%nat) b);
      destruct x as [|x]; destruct y as [|y]; reflexivity.
Qed.

Definition zind (m : mono) : Z := if forallb (Nat.eqb 0%nat) m then 1 else 0.

Lemma const_coef_ksum f : const_coef f = ksum f zind.
Proof.
  induction f as [|t f IH]; [reflexivity|].
  rewrite ksum_cons, <- IH.
  change (const_coef (t :: f)) with ((if forallb (Nat.eqb 0%nat) (fst t) then snd t else 0) + const_coef f).
  unfold zind. destruct (forallb (Nat.eqb 0%nat) (fst t)); ring.
Qed.

Lemma zind_madd a b : zind (madd a b) = zind a * zind b.
Proof.
  unfold zind. rewrite zmono_madd.
  destruct (forallb (Nat.eqb 0%nat) a), (forallb (Nat.eqb 0%nat) b); reflexivity.
Qed.

Lemma const_coef_pmul f g : const_coef (pmul f g) = const_coef f * const_coef g.
Proof.
  rewrite !const_coef_ksum, ksum_pmul.
  assert (E : forall a, ksum g (fun b => zind (madd a b)) = zind a * ksum g zind).
  { intros a. rewrite (ksum_ext g _ (fun b => zind a * zind b) (fun b => zind_madd a b)).
    apply ksum_scale_fun. }
  rewrite (ksum_ext f _ _ E).
  induction f as [|t f IH]; [reflexivity|].
  rewrite !ksum_cons. rewrite IH. ring.
Qed.

Lemma unit_mul p a b : prime p -> ~ cg p a 0 -> ~ cg p b 0 -> ~ cg p (a * b) 0.
Proof.
  intros Hp Ha Hb H. unfold cg in *. rewrite Z.sub_0_r in Ha, Hb, H.
  apply (proj1 (Z.divide_prime_mul a b p (proj2 (prime_alt p) Hp))) in H.
  destruct H as [H|H]; contradiction.
Qed.

Lemma LI_add p n gens f f' : prime p -> LI p n gens f -> LI p n gens f' -> LI p n gens (f ++ f').
Proof.
  intros Hp [u1 [Hu1 [Hn1 H1]]] [u2 [Hu2 [Hn2 H2]]].
  exists (pmul u1 u2). split; [apply wf_pmul; assumption|].
  split; [rewrite const_coef_pmul; apply unit_mul; assumption|].
  assert (E : se (pmul (pmul u1 u2) (f ++ f')) (pmul u2 (pmul u1 f) ++ pmul u1 (pmul u2 f'))).
  { transitivity (pmul (pmul u1 u2) f ++ pmul (pmul u1 u2) f').
    - apply se_pmul_app_r.
    - apply app_se.
      + rewrite (se_pmul_comm u1 u2). apply se_pmul_assoc.
      + apply se_pmul_assoc. }
  apply (Idl_se p n gens _ _ E).
  apply Idl_add; apply Idl_scalep; assumption.
Qed.

(** * Products and monomials of the generators *)

Lemma se_pow_add n g : wf_poly n g -> forall a b,
  se (pow_poly n g (a + b)%nat) (pmul (pow_poly n g a) (pow_poly n g b)).
Proof.
  intros Hg a b. induction a as [|a IH].
  - cbn [pow_poly Nat.add]. symmetry. apply se_pmul_one_l. apply wf_pow. exact Hg.
  - cbn [pow_poly Nat.add]. rewrite IH. symmetry. apply se_pmul_assoc.
Qed.

Lemma prod_ymono n G : Forall (wf_poly n) G -> forall d rho, In rho (products n G d) ->
  exists e, length e = length G /\ msum e = d /\ se rho (ymono n G e).
Proof.
  intros HG. induction G as [|g G IH]; intros d; induction d as [|d IHd]; intros rho Hin.
  - rewrite products_0 in Hin. destruct Hin as [<-|[]].
    exists []. split; [reflexivity|]. split; [reflexivity|]. reflexivity.
  - rewrite products_nil_S in Hin. destruct Hin.
  - rewrite products_0 in Hin. destruct Hin as [<-|[]].
    destruct (IH (Forall_inv_tail HG) 0%nat (one_poly n) (or_introl eq_refl)) as [e' [Hl [Hs Hse]]].
    exists (0%nat :: e'). split; [cbn [length]; f_equal; exact Hl|]. split; [cbn [msum]; exact Hs|].
    change (ymono n (g :: G) (0%nat :: e')) with (pmul (one_poly n) (ymono n G e')).
    transitivity (ymono n G e'); [exact Hse|].
    symmetry. apply se_pmul_one_l. apply wf_ymono. exact (Forall_inv_tail HG).
  - rewrite products_cons_S in Hin. apply in_app_iff in Hin as [Hin|Hin].
    + apply in_map_iff in Hin as [rho' [<- Hin]].
      destruct (IHd rho' Hin) as [e [Hl [Hs Hse]]].
      destruct e as [|k e]; [discriminate Hl|].
      cbn [length] in Hl. cbn [msum] in Hs.
      exists (S k :: e). split; [cbn [length]; exact Hl|]. split; [cbn [msum]; lia|].
      change (ymono n (g :: G) (S k :: e)) with (pmul (pmul g (pow_poly n g k)) (ymono n G e)).
      change (ymono n (g :: G) (k :: e)) with (pmul (pow_poly n g k) (ymono n G e)) in Hse.
      rewrite Hse. symmetry. apply se_pmul_assoc.
    + destruct (IH (Forall_inv_tail HG) (S d) rho Hin) as [e' [Hl [Hs Hse]]].
      exists (0%nat :: e'). split; [cbn [length]; f_equal; exact Hl|]. split; [cbn [msum]; exact Hs|].
      change (ymono n (g :: G) (0%nat :: e')) with (pmul (one_poly n) (ymono n G e')).
      transitivity (ymono n G e'); [exact Hse|].
      symmetry. apply se_pmul_one_l. apply wf_ymono. exact (Forall_inv_tail HG).
Qed.

Lemma products_tail n g G s rho : In rho (products n G s) -> In rho (products n (g :: G) s).
Proof.
  intros H. destruct s as [|s].
  - rewrite products_0 in H. rewrite products_0. exact H.
  - rewrite products_cons_S. apply in_or_app. right. exact H.
Qed.

Lemma pow_mul_products n g G (Hg : wf_poly n g) k s Y rho' :
  wf_poly n Y -> In rho' (products n G s) -> se Y rho' ->
  exists rho, In rho (products n (g :: G) (k + s)%nat) /\ se (pmul (pow_poly n g k) Y) rho.
Proof.
  intros HY Hin Hse. induction k as [|k IH].
  - exists rho'. split; [apply products_tail; exact Hin|].
    change (pow_poly n g 0) with (one_poly n).
    transitivity Y; [apply se_pmul_one_l; exact HY | exact Hse].
  - destruct IH as [rho [Hrho Hse2]]. exists (pmul g rho). split.
    + change (S k + s)%nat with (S (k + s)%nat). rewrite products_cons_S. apply in_or_app. left.
      apply in_map_iff. exists rho. split; [reflexivity | exact Hrho].
    + change (pow_poly n g (S k)) with (pmul g (pow_poly n g k)).
      rewrite (se_pmul_assoc g (pow_poly n g k) Y), Hse2. reflexivity.
Qed.

Lemma ymono_prod n G : Forall (wf_poly n) G -> forall e, length e = length G ->
  exists rho, In rho (products n G (msum e)) /\ se (ymono n G e) rho.
Proof.
  intros HG. induction G as [|g G IH]; intros e Hl.
  - destruct e as [|k e]; [|discriminate Hl].
    exists (one_poly n). split; [|reflexivity].
    cbn [msum]. rewrite products_0. left. reflexivity.
  - destruct e as [|k e]; [discriminate Hl|].
    cbn [length] in Hl. injection Hl as Hl.
    destruct (IH (Forall_inv_tail HG) e Hl) as [rho' [Hin Hse]].
    destruct (pow_mul_products n g G (Forall_inv HG) k (msum e) (ymono n G e) rho'
      (wf_ymono n G (Forall_inv_tail HG) e) Hin Hse) as [rho [Hrho Hse2]].
    exists rho. split; [exact Hrho | exact Hse2].
Qed.

Lemma ymono_madd n G : Forall (wf_poly n) G -> forall a b,
  length a = length G -> length b = length G ->
  se (ymono n G (madd a b)) (pmul (ymono n G a) (ymono n G b)).
Proof.
  intros HG. induction G as [|g G IH]; intros a b Ha Hb.
  - destruct a; [|discriminate Ha]. destruct b; [|discriminate Hb].
    change (se (one_poly n) (pmul (one_poly n) (one_poly n))).
    symmetry. apply se_pmul_one_l. apply wf_one.
  - destruct a as [|x a]; [discriminate Ha|]. destruct b as [|y b]; [discriminate Hb|].
    cbn [length] in Ha, Hb. injection Ha as Ha. injection Hb as Hb.
    change (madd (x :: a) (y :: b)) with ((x + y)%nat :: madd a b).
    change (ymono n (g :: G) ((x + y)%nat :: madd a b))
      with (pmul (pow_poly n g (x + y)%nat) (ymono n G (madd a b))).
    change (ymono n (g :: G) (x :: a)) with (pmul (pow_poly n g x) (ymono n G a)).
    change (ymono n (g :: G) (y :: b)) with (pmul (pow_poly n g y) (ymono n G b)).
    rewrite (IH (Forall_inv_tail HG) a b Ha Hb).
    rewrite (se_pow_add n g (Forall_inv HG) x y).
    apply se_pmul_4.
Qed.

(** * Multiples of the quadrics *)

Lemma LI_mult_transport p n J G e m f : Forall (wf_poly n) G -> length m = length G ->
  LI p n (J ++ m_products n G e) f ->
  LI p n (J ++ m_products n G (msum m + e)) (pmul (ymono n G m) f).
Proof.
  intros HG Hm [u [Hu [Hn HI]]].
  exists u. split; [exact Hu|]. split; [exact Hn|].
  assert (Hpi : wf_poly n (ymono n G m)) by (apply wf_ymono; exact HG).
  apply (Idl_se p n _ (pmul u (pmul (ymono n G m) f)) (pmul (ymono n G m) (pmul u f))).
  { rewrite <- (se_pmul_assoc u (ymono n G m) f), (se_pmul_comm u (ymono n G m)),
      (se_pmul_assoc (ymono n G m) u f). reflexivity. }
  refine (Idl_gens_change p n (J ++ m_products n G e) (J ++ m_products n G (msum m + e))
    (ymono n G m) Hpi ?[Hg] (pmul u f) HI).
  intros g Hg. apply in_app_iff in Hg as [HgJ|Hgm].
  - apply Idl_mem; [apply in_or_app; left; exact HgJ | exact Hpi].
  - unfold m_products in Hgm. apply in_flat_map in Hgm as [k0 [Hk0 Hg']].
    apply in_map_iff in Hg' as [rho [<- Hrho]].
    destruct (prod_ymono n G HG e rho Hrho) as [b [Hlb [Hsb Hseb]]].
    destruct (ymono_prod n G HG (madd m b) (eq_trans (length_madd m b (eq_trans Hm (eq_sym Hlb))) Hm))
      as [rho' [Hrho' Hserho']].
    rewrite msum_madd, Hsb in Hrho'.
    assert (Hs : se (pmul (ymono n G m) (pmul (var n k0) rho)) (pmul (var n k0) rho')).
    { rewrite <- (se_pmul_assoc (ymono n G m) (var n k0) rho), (se_pmul_comm (ymono n G m) (var n k0)),
        (se_pmul_assoc (var n k0) (ymono n G m) rho).
      rewrite Hseb.
      rewrite <- (ymono_madd n G HG m b Hm Hlb).
      rewrite Hserho'. reflexivity. }
    apply (Idl_se p n _ _ _ Hs).
    apply Idl_memw.
    + apply in_or_app. right. unfold m_products. apply in_flat_map. exists k0. split; [exact Hk0|].
      apply in_map_iff. exists rho'. split; [reflexivity | exact Hrho'].
    + apply wf_pmul; [apply wf_var | exact (wf_products n G HG _ rho' Hrho')].
Qed.

Lemma LI_nthq p n J G Q : prime p ->
  (forall q, In q Q -> LI p n (J ++ m_products n G 2) (subst_q n G q)) ->
  forall i, LI p n (J ++ m_products n G 2) (subst_q n G (nth i Q [])).
Proof.
  intros Hp HQ i.
  destruct (Nat.lt_ge_cases i (length Q)) as [Hlt|Hge].
  - apply HQ. apply nth_In. exact Hlt.
  - rewrite (nth_overflow Q [] Hge). exact (LI_nil p n _ Hp).
Qed.

(** * The substitution y -> G on identities *)

Definition qy (q : list (Z * list nat)) : poly := map (fun t => (snd t, fst t)) q.

Lemma qy_cons t q : qy (t :: q) = (snd t, fst t) :: qy q.
Proof. reflexivity. Qed.

Lemma ksum_subst_q n G q F :
  ksum (subst_q n G q) F = ksum (qy q) (fun a => ksum (ymono n G a) F).
Proof.
  induction q as [|t q IH]; [reflexivity|].
  assert (E : subst_q n G (t :: q)
    = map (fun x => (fst x, fst t * snd x)) (ymono n G (snd t)) ++ subst_q n G q) by reflexivity.
  rewrite E, ksum_app, ksum_scale_list, IH, qy_cons, ksum_cons. cbn [fst snd]. reflexivity.
Qed.

Lemma ksum_term n G : Forall (wf_poly n) G -> forall q m a F,
  length m = length G -> (forall t, In t q -> length (snd t) = length G) ->
  ksum (kb_scale a (pmul (ymono n G m) (subst_q n G q))) F
  = ksum (pmul [(m, a)] (qy q)) (fun b => ksum (ymono n G b) F).
Proof.
  intros HG q m a F Hm Hq.
  rewrite ksum_kb_scale, !ksum_pmul, ksum_single. cbv beta.
  f_equal.
  assert (E1 : forall u, ksum (subst_q n G q) (fun c => F (madd u c))
    = ksum (qy q) (fun b => ksum (ymono n G b) (fun c => F (madd u c)))) by (intros u; apply ksum_subst_q).
  rewrite (ksum_ext (ymono n G m) _ _ E1).
  pose proof (ksum_swap (ymono n G m) (qy q) (fun u b => ksum (ymono n G b) (fun c => F (madd u c)))) as E2.
  cbv beta in E2. rewrite E2.
  apply ksum_ext_in. intros t Ht. cbv beta.
  assert (Hlt : length (fst t) = length G).
  { unfold qy in Ht. apply in_map_iff in Ht as [t0 [<- Ht0]]. cbn [fst]. exact (Hq t0 Ht0). }
  rewrite (ymono_madd n G HG m (fst t) Hm Hlt F), ksum_pmul; try reflexivity.
Qed.

Fixpoint rsum_y (Q : list (list (Z * list nat))) (ms : list (nat * mono * Z)) : poly :=
  match ms with
  | [] => []
  | x :: r => pmul [(snd (fst x), snd x)] (qy (nth (fst (fst x)) Q [])) ++ rsum_y Q r
  end.

Fixpoint rsum_x (n : nat) (G : list poly) (Q : list (list (Z * list nat))) (ms : list (nat * mono * Z)) : poly :=
  match ms with
  | [] => []
  | x :: r =>
    kb_scale (snd x) (pmul (ymono n G (snd (fst x))) (subst_q n G (nth (fst (fst x)) Q []))) ++ rsum_x n G Q r
  end.

Lemma nth_q_ok (G : list poly) (Q : list (list (Z * list nat))) : Forall (fun q => forall t, In t q -> length (snd t) = length G) Q ->
  forall i t, In t (nth i Q []) -> length (snd t) = length G.
Proof.
  intros H i t Ht.
  destruct (Nat.lt_ge_cases i (length Q)) as [Hlt|Hge].
  - rewrite Forall_forall in H. exact (H _ (nth_In Q [] Hlt) t Ht).
  - rewrite (nth_overflow Q [] Hge) in Ht. destruct Ht.
Qed.

Lemma rsum_ksum n G Q : Forall (wf_poly n) G ->
  Forall (fun q => forall t, In t q -> length (snd t) = length G) Q ->
  forall ms F, (forall x, In x ms -> length (snd (fst x)) = length G) ->
  ksum (rsum_x n G Q ms) F = ksum (rsum_y Q ms) (fun a => ksum (ymono n G a) F).
Proof.
  intros HG HQ. induction ms as [|x ms IH]; intros F Hms; [reflexivity|].
  change (rsum_x n G Q (x :: ms)) with (kb_scale (snd x) (pmul (ymono n G (snd (fst x))) (subst_q n G (nth (fst (fst x)) Q []))) ++ rsum_x n G Q ms).
  change (rsum_y Q (x :: ms)) with (pmul [(snd (fst x), snd x)] (qy (nth (fst (fst x)) Q [])) ++ rsum_y Q ms).
  rewrite !ksum_app, (IH F (fun y Hy => Hms y (or_intror Hy))).
  rewrite (ksum_term n G HG (nth (fst (fst x)) Q []) (snd (fst x)) (snd x) F
    (Hms x (or_introl eq_refl)) (nth_q_ok G Q HQ (fst (fst x)))); try reflexivity.
Qed.

Lemma rsum_LI p n J G d Q : prime p -> Forall (wf_poly n) G -> (2 <= d)%nat ->
  (forall q, In q Q -> LI p n (J ++ m_products n G 2) (subst_q n G q)) ->
  forall ms, (forall x, In x ms -> length (snd (fst x)) = length G /\ msum (snd (fst x)) = (d - 2)%nat) ->
  LI p n (J ++ m_products n G d) (rsum_x n G Q ms).
Proof.
  intros Hp HG Hd HQ ms. induction ms as [|x ms IH]; intros Hms.
  - exact (LI_nil p n _ Hp).
  - cbn [rsum_x]. apply LI_add; [exact Hp | | apply IH; intros y Hy; apply Hms; right; exact Hy].
    destruct (Hms x (or_introl eq_refl)) as [Hl Hs].
    apply LI_scalec.
    assert (Hdd : d = (msum (snd (fst x)) + 2)%nat) by lia.
    rewrite Hdd.
    apply LI_mult_transport; [exact HG | exact Hl |].
    apply LI_nthq; assumption.
Qed.

(** * The identity y^mu = sum of multiples and standard monomials *)

Record red_entry := mk_red { r_mu : mono; r_mult : list (nat * mono * Z); r_std : list (mono * Z) }.

Definition rhs_y (Q : list (list (Z * list nat))) (e : red_entry) : poly :=
  rsum_y Q (r_mult e) ++ r_std e.

Fixpoint tmults (Q : list (list (Z * list nat))) (t : tr) (ms : list (nat * mono * Z)) : tr :=
  match ms with
  | [] => t
  | x :: r => tmults Q (tmul (-1) t [(snd (fst x), snd x)] (qy (nth (fst (fst x)) Q []))) r
  end.

Fixpoint tstds (t : tr) (ss : list (mono * Z)) : tr :=
  match ss with
  | [] => t
  | x :: r => tstds (tadd t (enc (fst x)) (- snd x)) r
  end.

Definition ident_tr (Q : list (list (Z * list nat))) (e : red_entry) : tr :=
  tstds (tmults Q (tadd TL (enc (r_mu e)) 1) (r_mult e)) (r_std e).

Lemma tget_tstds ss : forall t m, tget (tstds t ss) (enc m) = tget t (enc m) - pcoef ss m.
Proof.
  induction ss as [|s ss IH]; intros t m.
  - cbn [tstds]. rewrite pcoef_nil. ring.
  - cbn [tstds]. rewrite IH, tadd_enc, pcoef_cons.
    destruct (mono_eq_dec (fst s) m); cbn [snd]; ring.
Qed.

Lemma tget_tmults Q ms : forall t m, tget (tmults Q t ms) (enc m) = tget t (enc m) - pcoef (rsum_y Q ms) m.
Proof.
  induction ms as [|x r IH]; intros t m.
  - cbn [tmults rsum_y]. rewrite pcoef_nil. ring.
  - cbn [tmults rsum_y]. rewrite IH, tmul_get, pcoef_app. ring.
Qed.

Lemma ident_sound p Q e : tall p (ident_tr Q e) = true ->
  forall F, cg p (ksum [(r_mu e, 1)] F) (ksum (rhs_y Q e) F).
Proof.
  intros H. apply (proj2 (pe_pzero p _ _)). intros m.
  pose proof (tall_sound p _ H (enc m)) as E.
  unfold ident_tr in E. rewrite tget_tstds, tget_tmults, tadd_enc in E.
  replace (tget TL (enc m)) with 0 in E by reflexivity.
  unfold padd. rewrite pcoef_app, pcoef_pneg. unfold rhs_y. rewrite pcoef_app.
  rewrite pcoef_cons, pcoef_nil. cbn [fst snd].
  apply cg_zero_of_mod. etransitivity; [|exact E]. f_equal. ring.
Qed.

Definition std_cs (S : list mono) (ss : list (mono * Z)) : list Z := map (kcoef mono_eq_dec ss) S.

Lemma ksum_lincomb_std n G S ss F :
  ksum (lincomb (map (kcoef mono_eq_dec ss) S) (map (ymono n G) S)) F
  = gsumk mono_eq_dec S ss (fun a => ksum (ymono n G a) F).
Proof.
  induction S as [|s S IH]; [reflexivity|].
  cbn [map lincomb gsumk]. rewrite ksum_app, ksum_scale_list, IH. reflexivity.
Qed.

Lemma entry_sound p n J G d Q S e :
  prime p -> Forall (wf_poly n) G -> (2 <= d)%nat ->
  (forall q, In q Q -> LI p n (J ++ m_products n G 2) (subst_q n G q)) ->
  Forall (fun q => forall t, In t q -> length (snd t) = length G) Q ->
  NoDup S ->
  (forall x, In x (r_mult e) -> length (snd (fst x)) = length G /\ msum (snd (fst x)) = (d - 2)%nat) ->
  (forall t, In t (r_std e) -> In (fst t) S) ->
  tall p (ident_tr Q e) = true ->
  LI p n (J ++ m_products n G d)
    (padd (ymono n G (r_mu e)) (pneg (lincomb (std_cs S (r_std e)) (map (ymono n G) S)))).
Proof.
  intros Hp HG Hd HQ HQl Hnd Hmult Hstd Htall.
  apply (LI_pe p n _ _ (rsum_x n G Q (r_mult e))).
  - intros F.
    unfold padd, pneg. rewrite ksum_app, ksum_neg_list.
    unfold std_cs. rewrite ksum_lincomb_std.
    rewrite <- (ksum_group mono_eq_dec (r_std e) S (fun a => ksum (ymono n G a) F) Hnd Hstd).
    rewrite (rsum_ksum n G Q HG HQl (r_mult e) F (fun x Hx => proj1 (Hmult x Hx))).
    pose proof (ident_sound p Q e Htall (fun a => ksum (ymono n G a) F)) as Hid.
    unfold rhs_y in Hid. rewrite ksum_app, ksum_single in Hid. cbv beta in Hid.
    apply cg_rearr. exact Hid.
  - apply rsum_LI; assumption.
Qed.

(** * The bound certificate and its checker *)

Definition mono_eqb (a b : mono) : bool := if mono_eq_dec a b then true else false.

Lemma mono_eqb_true a b : mono_eqb a b = true -> a = b.
Proof.
  unfold mono_eqb. destruct (mono_eq_dec a b) as [E|E]; intros H; [exact E | discriminate H].
Qed.

Lemma mono_eqb_refl a : mono_eqb a a = true.
Proof. unfold mono_eqb. destruct (mono_eq_dec a a) as [E|E]; [reflexivity | contradiction]. Qed.

Fixpoint nodup_b (l : list mono) : bool :=
  match l with
  | [] => true
  | x :: l' => negb (existsb (mono_eqb x) l') && nodup_b l'
  end.

Lemma nodup_b_sound l : nodup_b l = true -> NoDup l.
Proof.
  induction l as [|x l IH]; intros H; [constructor|].
  cbn [nodup_b] in H. apply andb_true_iff in H as [H1 H2].
  constructor; [|apply IH; exact H2].
  intros Hin. apply negb_true_iff in H1.
  assert (H3 : existsb (mono_eqb x) l = true).
  { apply existsb_exists. exists x. split; [exact Hin | apply mono_eqb_refl]. }
  congruence.
Qed.

Fixpoint all_monos (k d : nat) : list mono :=
  match k with
  | O => match d with O => [[]] | S _ => [] end
  | S k' => flat_map (fun e => map (cons e) (all_monos k' (d - e)%nat)) (seq 0 (S d))
  end.

Lemma all_monos_complete : forall k d mu, length mu = k -> msum mu = d -> In mu (all_monos k d).
Proof.
  induction k as [|k IH]; intros d mu Hl Hs.
  - destruct mu as [|x mu]; [|discriminate Hl].
    cbn [msum] in Hs. subst d. cbn [all_monos]. left. reflexivity.
  - destruct mu as [|x mu]; [discriminate Hl|].
    cbn [length] in Hl. injection Hl as Hl.
    cbn [msum] in Hs. cbn [all_monos]. apply in_flat_map. exists x. split.
    + apply (proj2 (in_seq (S d) 0 x)). split; lia.
    + apply in_map_iff. exists mu. split; [reflexivity|].
      apply IH; [exact Hl | lia].
Qed.

Definition std_entries (S : list mono) : list red_entry := map (fun s => mk_red s [] [(s, 1)]) S.

Definition check_entry (p : Z) (ny : nat) (Q : list (list (Z * list nat))) (d : nat) (S : list mono)
  (e : red_entry) : bool :=
  Nat.eqb (length (r_mu e)) ny && Nat.eqb (msum (r_mu e)) d &&
  forallb (fun x => Nat.ltb (fst (fst x)) (length Q) &&
    (Nat.eqb (length (snd (fst x))) ny && Nat.eqb (msum (snd (fst x))) (d - 2)%nat)) (r_mult e) &&
  forallb (fun t => existsb (mono_eqb (fst t)) S) (r_std e) &&
  tall p (ident_tr Q e).

Lemma check_entry_facts p ny Q d S e : check_entry p ny Q d S e = true ->
  (forall x, In x (r_mult e) -> length (snd (fst x)) = ny /\ msum (snd (fst x)) = (d - 2)%nat) /\
  (forall t, In t (r_std e) -> In (fst t) S) /\
  tall p (ident_tr Q e) = true.
Proof.
  unfold check_entry. intros H.
  apply andb_prop in H as [H Ed]. apply andb_prop in H as [H Ec]. apply andb_prop in H as [_ Eb].
  split; [|split; [|exact Ed]].
  - intros x Hx. rewrite forallb_forall in Eb. pose proof (Eb x Hx) as Eb'.
    apply andb_true_iff in Eb' as [_ Eb'].
    apply andb_true_iff in Eb' as [Eb1 Eb2]. split; apply Nat.eqb_eq; assumption.
  - intros t Ht. rewrite forallb_forall in Ec. pose proof (Ec t Ht) as Ec'.
    apply existsb_exists in Ec' as [s [Hs Hes]]. apply mono_eqb_true in Hes. rewrite Hes. exact Hs.
Qed.

(** The reduction checker: the degree, the generators, the quadrics as data, the standard monomials, every
    reduction entry and the coverage of all monomials of degree d. It checks no membership of a quadric in the
    local ideal: [hilbert_upper_bound_of_red] takes that as a hypothesis, which any certificate can supply. *)
Definition check_red (p : Z) (n : nat) (G : list poly) (d : nat) (Q : list (list (Z * list nat)))
  (S : list mono) (red : list red_entry) : bool :=
  Nat.leb 2 d &&
  forallb (wf_b n) G &&
  forallb (fun q => forallb (fun t => Nat.eqb (length (snd t)) (length G)) q) Q &&
  forallb (fun s => Nat.eqb (length s) (length G) && Nat.eqb (msum s) d) S &&
  nodup_b S &&
  forallb (check_entry p (length G) Q d S) (std_entries S ++ red) &&
  forallb (fun mu => existsb (fun e => mono_eqb (r_mu e) mu) (std_entries S ++ red))
    (all_monos (length G) d).

(** The monolithic checker: the reduction checker and the unfactored cofactor certificate of every quadric. *)
Definition check_bound (p : Z) (n : nat) (J G : list poly) (d : nat) (Q : list (list (Z * list nat)))
  (cs : list kcert) (S : list mono) (red : list red_entry) : bool :=
  check_red p n G d Q S red &&
  Nat.eqb (length cs) (length Q) &&
  forallb (fun qc => check_cofactor p n J G 2 (fst qc) (snd qc)) (combine Q cs).

Lemma in_combine_ex {A B : Type} (l : list A) (l' : list B) x :
  length l' = length l ->
  In x l -> exists y, In (x, y) (combine l l').
Proof.
  revert l'. induction l as [|a l IH]; intros l' Hl Hin.
  - destruct Hin.
  - destruct l' as [|b l']; [discriminate Hl|].
    destruct Hin as [E|Hin].
    + exists b. left. subst. reflexivity.
    + injection Hl as Hl. destruct (IH l' Hl Hin) as [y Hy]. exists y. right. exact Hy.
Qed.

Lemma check_bound_red p n J G d Q cs S red : check_bound p n J G d Q cs S red = true ->
  check_red p n G d Q S red = true.
Proof.
  unfold check_bound. intros H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. exact H.
Qed.

Lemma check_bound_members p n J G d Q cs S red : check_bound p n J G d Q cs S red = true ->
  forall q, In q Q -> LI p n (J ++ m_products n G 2) (subst_q n G q).
Proof.
  unfold check_bound. intros H q Hq.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [_ H3].
  destruct (in_combine_ex Q cs q (proj1 (Nat.eqb_eq _ _) H3) Hq) as [c Hqc].
  rewrite forallb_forall in H4. pose proof (H4 (q, c) Hqc) as H4'. cbn [fst snd] in H4'.
  apply LI_of_ili. exact (check_cofactor_sound _ _ _ _ _ _ _ H4').
Qed.

Lemma check_red_facts p n G d Q S red : check_red p n G d Q S red = true ->
  Forall (wf_poly n) G /\ (forall s, In s S -> length s = length G /\ msum s = d).
Proof.
  intros H. unfold check_red in H.
  apply andb_prop in H as [H H9]. apply andb_prop in H as [H H8]. apply andb_prop in H as [H H7].
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H1 H2].
  split.
  - apply Forall_forall. intros g Hg. rewrite forallb_forall in H2. apply wf_b_sound. exact (H2 g Hg).
  - intros s Hs. rewrite forallb_forall in H6. pose proof (H6 s Hs) as H6'.
    apply andb_prop in H6' as [Ha Hb]. split; apply Nat.eqb_eq; assumption.
Qed.

Lemma check_bound_facts p n J G d Q cs S red : check_bound p n J G d Q cs S red = true ->
  Forall (wf_poly n) G /\ (forall s, In s S -> length s = length G /\ msum s = d).
Proof. intros H. exact (check_red_facts p n G d Q S red (check_bound_red _ _ _ _ _ _ _ _ _ H)). Qed.

(** Spanning from the reduction checker and an external membership hypothesis for each quadric. *)
Theorem hilbert_upper_bound_of_red p n J G d Q S red : prime p ->
  check_red p n G d Q S red = true ->
  (forall q, In q Q -> LI p n (J ++ m_products n G 2) (subst_q n G q)) ->
  spans_mod p n (J ++ m_products n G d) (products n G d) (map (ymono n G) S).
Proof.
  intros Hp H HQ. unfold check_red in H.
  apply andb_prop in H as [H H9]. apply andb_prop in H as [H H8]. apply andb_prop in H as [H H7].
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H1 H2].
  assert (Hd : (2 <= d)%nat) by (apply Nat.leb_le; exact H1).
  assert (HG : Forall (wf_poly n) G).
  { apply Forall_forall. intros g Hg. rewrite forallb_forall in H2. apply wf_b_sound. exact (H2 g Hg). }
  assert (HQl : Forall (fun q => forall t, In t q -> length (snd t) = length G) Q).
  { apply Forall_forall. intros q Hq t Ht. rewrite forallb_forall in H5.
    pose proof (H5 q Hq) as H5'. rewrite forallb_forall in H5'.
    apply Nat.eqb_eq. exact (H5' t Ht). }
  pose proof (nodup_b_sound S H7) as Hnd.
  intros rho Hrho.
  destruct (prod_ymono n G HG d rho Hrho) as [mu [Hlmu [Hsmu Hserho]]].
  assert (Hmu : In mu (all_monos (length G) d)) by (apply all_monos_complete; assumption).
  rewrite forallb_forall in H9. pose proof (H9 mu Hmu) as H9'.
  apply existsb_exists in H9' as [e [He Hme]]. apply mono_eqb_true in Hme. subst mu.
  rewrite forallb_forall in H8. pose proof (H8 e He) as H8'.
  destruct (check_entry_facts _ _ _ _ _ _ H8') as [Hmult [Hstd Ed]].
  pose proof (entry_sound p n J G d Q S e Hp HG Hd HQ HQl Hnd Hmult Hstd Ed) as HL.
  exists (std_cs S (r_std e)). split; [unfold std_cs; rewrite !length_map; reflexivity|].
  apply ili_of_LI.
  refine (LI_pe p n _ _ _ ?[Hrel] HL).
  intros F. unfold padd, pneg. rewrite !ksum_app, !ksum_neg_list, (Hserho F). apply cg_refl.
Qed.

Theorem hilbert_upper_bound p n J G d Q cs S red : prime p ->
  check_bound p n J G d Q cs S red = true ->
  spans_mod p n (J ++ m_products n G d) (products n G d) (map (ymono n G) S).
Proof.
  intros Hp H. exact (hilbert_upper_bound_of_red p n J G d Q S red Hp (check_bound_red _ _ _ _ _ _ _ _ _ H)
    (check_bound_members _ _ _ _ _ _ _ _ _ H)).
Qed.

(** * Spanning by selected products *)

Lemma ksum_lincomb_se : forall r r', Forall2 se r r' -> forall cs F,
  ksum (lincomb cs r) F = ksum (lincomb cs r') F.
Proof.
  intros r r' H. induction H as [|P P' r r' HP Hr IH]; intros cs F; [destruct cs; reflexivity|].
  destruct cs as [|c cs]; [reflexivity|].
  cbn [lincomb]. rewrite !ksum_app, !ksum_scale_list, (IH cs F), (HP F). reflexivity.
Qed.

Lemma spans_mod_se p n gens Pr reps reps' :
  Forall2 se reps reps' -> spans_mod p n gens Pr reps' -> spans_mod p n gens Pr reps.
Proof.
  intros Hse Hs rho Hrho. destruct (Hs rho Hrho) as [cs [Hl Hi]].
  assert (Hl2 : length reps = length reps') by exact (Forall2_length Hse).
  exists cs. split; [rewrite Hl2; exact Hl|].
  apply ili_of_LI. refine (LI_pe p n _ _ _ ?[Hrel] (LI_of_ili p n _ _ Hi)).
  intros F. unfold padd, pneg. rewrite !ksum_app, !ksum_neg_list, (ksum_lincomb_se _ _ Hse cs F).
  apply cg_refl.
Qed.

Lemma exists_sel n G d S : (forall s, In s S -> length s = length G /\ msum s = d) -> Forall (wf_poly n) G ->
  exists sel, length sel = length S /\ (forall i, In i sel -> (i < length (products n G d))%nat) /\
    Forall2 se (select_products n G d sel) (map (ymono n G) S).
Proof.
  intros HS HG. induction S as [|s S IH].
  - exists []. split; [reflexivity|]. split; [intros i []|]. constructor.
  - destruct (HS s (or_introl eq_refl)) as [Hl Hm].
    destruct (ymono_prod n G HG s Hl) as [rho [Hin Hse]].
    rewrite Hm in Hin.
    destruct (In_nth (products n G d) rho (one_poly n) Hin) as [i [Hi Hnth]].
    destruct (IH (fun s' Hs' => HS s' (or_intror Hs'))) as [sel [Hl' [Hr Hf]]].
    exists (i :: sel). split; [cbn [length]; f_equal; exact Hl'|]. split.
    + intros j [<-|Hj]; [exact Hi | apply Hr; exact Hj].
    + unfold select_products in *. cbn [map]. constructor.
      * rewrite Hnth. symmetry. exact Hse.
      * exact Hf.
Qed.

Theorem hilbert_upper_sel_of_red p n J G d Q S red : prime p ->
  check_red p n G d Q S red = true ->
  (forall q, In q Q -> LI p n (J ++ m_products n G 2) (subst_q n G q)) ->
  exists sel, length sel = length S /\ (forall i, In i sel -> (i < length (products n G d))%nat) /\
    spans_mod p n (J ++ m_products n G d) (products n G d) (select_products n G d sel).
Proof.
  intros Hp H HQ. destruct (check_red_facts p n G d Q S red H) as [HG HS].
  destruct (exists_sel n G d S HS HG) as [sel [Hl [Hr Hf]]].
  exists sel. split; [exact Hl|]. split; [exact Hr|].
  exact (spans_mod_se p n _ _ _ _ Hf (hilbert_upper_bound_of_red p n J G d Q S red Hp H HQ)).
Qed.

Theorem hilbert_cell_of_red p n J G d Q S red sel : prime p ->
  check_red p n G d Q S red = true ->
  (forall q, In q Q -> LI p n (J ++ m_products n G 2) (subst_q n G q)) ->
  (forall i, In i sel -> (i < length (products n G d))%nat) ->
  Forall2 se (select_products n G d sel) (map (ymono n G) S) ->
  independent_mod p n (J ++ m_products n G d) (select_products n G d sel) ->
  hilbert_cell p n J G d (length sel).
Proof.
  intros Hp H HQ Hr Hse Hind. exists sel. split; [reflexivity|]. split; [exact Hr|]. split; [exact Hind|].
  exact (spans_mod_se p n _ _ _ _ Hse (hilbert_upper_bound_of_red p n J G d Q S red Hp H HQ)).
Qed.

Theorem hilbert_upper_sel p n J G d Q cs S red : prime p ->
  check_bound p n J G d Q cs S red = true ->
  exists sel, length sel = length S /\ (forall i, In i sel -> (i < length (products n G d))%nat) /\
    spans_mod p n (J ++ m_products n G d) (products n G d) (select_products n G d sel).
Proof.
  intros Hp H. exact (hilbert_upper_sel_of_red p n J G d Q S red Hp (check_bound_red _ _ _ _ _ _ _ _ _ H)
    (check_bound_members _ _ _ _ _ _ _ _ _ H)).
Qed.

Theorem hilbert_cell_of_bound p n J G d Q cs S red sel : prime p ->
  check_bound p n J G d Q cs S red = true ->
  (forall i, In i sel -> (i < length (products n G d))%nat) ->
  Forall2 se (select_products n G d sel) (map (ymono n G) S) ->
  independent_mod p n (J ++ m_products n G d) (select_products n G d sel) ->
  hilbert_cell p n J G d (length sel).
Proof.
  intros Hp H Hr Hse Hind. exact (hilbert_cell_of_red p n J G d Q S red sel Hp (check_bound_red _ _ _ _ _ _ _ _ _ H)
    (check_bound_members _ _ _ _ _ _ _ _ _ H) Hr Hse Hind).
Qed.

(** * Calibration over F_7 *)

Definition kb_toy_J : list poly := [ [([5%nat], 1)] ].
Definition kb_toy_G : list poly := [ [([1%nat], 1)]; [([1%nat], 2)] ].
Definition kb_toy_Q : list (list (Z * list nat)) := [ [ (4, [2%nat; 0%nat]); (-1, [0%nat; 2%nat]) ] ].
Definition kb_toy_cof : list kcert := [ mk_kcert [([0%nat], 1)] [ []; []; []; [] ] ].
Definition kb_toy_S : list mono := [ [1%nat; 2%nat]; [0%nat; 3%nat] ].

Definition kb_toy_red : list red_entry :=
  [ mk_red [3%nat; 0%nat] [ ((0%nat, [1%nat; 0%nat]), 2) ] [ ([1%nat; 2%nat], 2) ];
    mk_red [2%nat; 1%nat] [ ((0%nat, [0%nat; 1%nat]), 2) ] [ ([0%nat; 3%nat], 2) ] ].

Definition kb_toy_check (red : list red_entry) : bool :=
  check_bound 7 1 kb_toy_J kb_toy_G 3 kb_toy_Q kb_toy_cof kb_toy_S red.

Lemma toy_bound_accepted : kb_toy_check kb_toy_red = true.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_coefficient_rejected :
  kb_toy_check [ mk_red [3%nat; 0%nat] [ ((0%nat, [1%nat; 0%nat]), 3) ] [ ([1%nat; 2%nat], 2) ];
                 mk_red [2%nat; 1%nat] [ ((0%nat, [0%nat; 1%nat]), 2) ] [ ([0%nat; 3%nat], 2) ] ] = false.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_multiplier_rejected :
  kb_toy_check [ mk_red [3%nat; 0%nat] [ ((0%nat, [0%nat; 1%nat]), 2) ] [ ([1%nat; 2%nat], 2) ];
                 mk_red [2%nat; 1%nat] [ ((0%nat, [0%nat; 1%nat]), 2) ] [ ([0%nat; 3%nat], 2) ] ] = false.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_standard_rejected :
  kb_toy_check [ mk_red [3%nat; 0%nat] [ ((0%nat, [1%nat; 0%nat]), 2) ] [ ([0%nat; 3%nat], 2) ];
                 mk_red [2%nat; 1%nat] [ ((0%nat, [0%nat; 1%nat]), 2) ] [ ([0%nat; 3%nat], 2) ] ] = false.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_missing_rejected :
  kb_toy_check [ mk_red [3%nat; 0%nat] [ ((0%nat, [1%nat; 0%nat]), 2) ] [ ([1%nat; 2%nat], 2) ] ] = false.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_index_rejected :
  kb_toy_check [ mk_red [3%nat; 0%nat] [ ((0%nat, [1%nat; 0%nat]), 2); ((1%nat, [1%nat; 0%nat]), 0) ] [ ([1%nat; 2%nat], 2) ];
                 mk_red [2%nat; 1%nat] [ ((0%nat, [0%nat; 1%nat]), 2) ] [ ([0%nat; 3%nat], 2) ] ] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem toy_bound :
  spans_mod 7 1 (kb_toy_J ++ m_products 1 kb_toy_G 3) (products 1 kb_toy_G 3)
    (map (ymono 1 kb_toy_G) kb_toy_S).
Proof. exact (hilbert_upper_bound 7 1 _ _ 3 _ _ _ _ prime_7 toy_bound_accepted). Qed.

(** The split form: [check_red] on its own, with the membership of the quadric supplied separately (here by
    the cofactor checker, but any proof of [LI] serves). *)
Lemma toy_red_accepted : check_red 7 1 kb_toy_G 3 kb_toy_Q kb_toy_S kb_toy_red = true.
Proof. vm_compute. reflexivity. Qed.

Theorem toy_bound_split :
  (forall q, In q kb_toy_Q -> LI 7 1 (kb_toy_J ++ m_products 1 kb_toy_G 2) (subst_q 1 kb_toy_G q)) ->
  spans_mod 7 1 (kb_toy_J ++ m_products 1 kb_toy_G 3) (products 1 kb_toy_G 3)
    (map (ymono 1 kb_toy_G) kb_toy_S).
Proof. intros HQ. exact (hilbert_upper_bound_of_red 7 1 _ _ 3 _ _ _ prime_7 toy_red_accepted HQ). Qed.

Print Assumptions hilbert_upper_bound_of_red.
Print Assumptions hilbert_upper_sel_of_red.
Print Assumptions hilbert_cell_of_red.
Print Assumptions hilbert_upper_bound.
Print Assumptions hilbert_upper_sel.
Print Assumptions hilbert_cell_of_bound.
Print Assumptions toy_bound.
Print Assumptions toy_bound_split.
