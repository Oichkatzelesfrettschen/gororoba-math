(** Factored cofactor checker: Horner grouping of the products t_i G_a G_b and normalized partial sums.

    Convention: a polynomial is the list of (monomial, coefficient) pairs of HilbertCellCertificate.v, repeated
    monomials allowed; [pcoef f m] sums the coefficients of the monomial m; [peq p f g] says every such sum of f
    is congruent to the sum of g modulo p; [tri k] is k (k+1) / 2, the number of products G_a G_b with
    a <= b of a list of k generators, in the order of [products n G 2]. The cofactor list holds one polynomial
    per generator of J ++ m_products n G 2: the first length J entries belong to J, then n blocks of [tri
    (length G)] entries, block i (t_i) in the order of [products n G 2]. The checker needs p > 0, where the
    plain checker [check_cofactor] of K2CofactorCertificate.v needs p <> 0; the Hilbert application of
    K2HilbertBoundFactored.v assumes prime p. The checker computes with the shapes of J, G and the cofactor
    list and builds no polynomial of m_products.

    Mechanism: a certificate shows that the polynomial f = q(G) lies in the local ideal of J ++ m_products n G 2 in the
    sense of [in_local_ideal] of HilbertCellCertificate.v: a unit u and one cofactor per generator with
    u f - sum_j cofs_j gens_j congruent to 0 modulo p in every coefficient. [check_factored] reads the cofactors
    b_{i,ab} of the generators t_i G_a G_b and forms, instead of the sum of the products b_{i,ab} (t_i G_a G_b),
    the grouping B_ab = sum_i t_i b_{i,ab}, H_a = sum_{b >= a} G_b B_ab and sum_a G_a H_a, where each B_ab and H_a
    is a normalized polynomial: [norm_poly] collects the terms of a list in a monomial trie, reads each
    monomial once, reduces the coefficient modulo p and drops the zero terms. The trie of u f - sum_k a_k J_k
    - sum_a G_a H_a is then tested coefficient by coefficient modulo p ([tall] of K2CofactorCertificate.v).

    Main results: [check_factored_sound] and [check_data_factored_sound] (an accepted certificate puts
    subst_q n G q in the local ideal of J ++ m_products n G 2, the conclusion of [check_cofactor_sound]
    of K2CofactorCertificate.v at d = 2); [norm_poly_peq] (normalization preserves a polynomial modulo p);
    [pmul_swap], [pmul_assoc], [pmul_comm] (the ring laws of pmul on coefficients); [horner] (the grouping);
    [toy_accepted_f] and four [_rejected_f] lemmas, and [toy_data_accepted_f] and [toy_data_rejected_f] (the
    decoded-data form through [decode_cert]), all on the one-variable cell over F_7 of K2CofactorCertificate.v. *)

From Stdlib Require Import ZArith Lia List Bool PeanoNat NArith.
Require Import HilbertCellCertificate K2CofactorCertificate.
Import ListNotations.
Open Scope Z_scope.

Definition Ssum {A : Type} (l : list A) (F : A -> Z) : Z := fold_right (fun a s => F a + s) 0 l.

Lemma Ssum_nil {A : Type} (F : A -> Z) : Ssum [] F = 0.
Proof. reflexivity. Qed.

Lemma Ssum_cons {A : Type} (a : A) (l : list A) (F : A -> Z) : Ssum (a :: l) F = F a + Ssum l F.
Proof. reflexivity. Qed.

Lemma Ssum_app {A : Type} (l1 l2 : list A) (F : A -> Z) : Ssum (l1 ++ l2) F = Ssum l1 F + Ssum l2 F.
Proof.
  induction l1 as [|a l1 IH]; [rewrite Ssum_nil; simpl app; lia|].
  simpl app. rewrite !Ssum_cons, IH. ring.
Qed.

Lemma Ssum_map {A B : Type} (g : A -> B) (l : list A) (F : B -> Z) :
  Ssum (map g l) F = Ssum l (fun a => F (g a)).
Proof.
  induction l as [|a l IH]; [reflexivity|].
  simpl map. rewrite !Ssum_cons, IH; try reflexivity.
Qed.

Lemma Ssum_flat_map {A B : Type} (g : A -> list B) (l : list A) (F : B -> Z) :
  Ssum (flat_map g l) F = Ssum l (fun a => Ssum (g a) F).
Proof.
  induction l as [|a l IH]; [reflexivity|].
  simpl flat_map. rewrite Ssum_app, !Ssum_cons, IH; try reflexivity.
Qed.

Lemma Ssum_ext {A : Type} (l : list A) (F G : A -> Z) :
  (forall a, In a l -> F a = G a) -> Ssum l F = Ssum l G.
Proof.
  induction l as [|a l IH]; intros H; [reflexivity|].
  rewrite !Ssum_cons. rewrite (H a (or_introl eq_refl)).
  rewrite (IH (fun b Hb => H b (or_intror Hb))); try reflexivity.
Qed.

Lemma Ssum_add {A : Type} (l : list A) (F G : A -> Z) :
  Ssum l (fun a => F a + G a) = Ssum l F + Ssum l G.
Proof.
  induction l as [|a l IH]; [reflexivity|].
  rewrite !Ssum_cons, IH. cbv beta. ring.
Qed.

Lemma Ssum_opp {A : Type} (l : list A) (F : A -> Z) :
  Ssum l (fun a => - F a) = - Ssum l F.
Proof.
  induction l as [|a l IH]; [reflexivity|].
  rewrite !Ssum_cons, IH. cbv beta. ring.
Qed.

Lemma Ssum_zero {A : Type} (l : list A) : Ssum l (fun _ => 0) = 0.
Proof.
  induction l as [|a l IH]; [reflexivity|].
  rewrite Ssum_cons, IH. cbv beta. lia.
Qed.

Lemma Ssum_swap {A B : Type} (l : list A) (l' : list B) (F : A -> B -> Z) :
  Ssum l (fun a => Ssum l' (fun b => F a b)) = Ssum l' (fun b => Ssum l (fun a => F a b)).
Proof.
  induction l as [|a l IH].
  - rewrite Ssum_nil. symmetry. etransitivity.
    + apply Ssum_ext. intros b _. apply Ssum_nil.
    + apply Ssum_zero.
  - rewrite Ssum_cons, IH. rewrite <- Ssum_add. apply Ssum_ext. intros b _.
    rewrite Ssum_cons. cbv beta. reflexivity.
Qed.

Lemma Ssum_cg0 {A : Type} (p : Z) (l : list A) (F : A -> Z) :
  (forall a, In a l -> cg p (F a) 0) -> cg p (Ssum l F) 0.
Proof.
  induction l as [|a l IH]; intros H; [apply cg_refl|].
  rewrite Ssum_cons. apply cg_zero_add.
  - apply H. left. reflexivity.
  - apply IH. intros b Hb. apply H. right. exact Hb.
Qed.

Lemma pcoef_Ssum (f : poly) (m : mono) :
  pcoef f m = Ssum f (fun s => if mono_eq_dec (fst s) m then snd s else 0).
Proof.
  induction f as [|s f IH]; [reflexivity|].
  rewrite pcoef_cons, Ssum_cons, IH; try reflexivity.
Qed.

Lemma pcoef_pmul (f g : poly) (m : mono) :
  pcoef (pmul f g) m =
  Ssum f (fun s => Ssum g (fun t => if mono_eq_dec (madd (fst s) (fst t)) m then snd s * snd t else 0)).
Proof.
  rewrite pcoef_Ssum. unfold pmul. rewrite Ssum_flat_map.
  apply Ssum_ext. intros s _. apply Ssum_map.
Qed.

Lemma Ssum_pmul (f g : poly) (F : mono * Z -> Z) :
  Ssum (pmul f g) F = Ssum f (fun s => Ssum g (fun t => F (madd (fst s) (fst t), snd s * snd t))).
Proof.
  unfold pmul. rewrite Ssum_flat_map. apply Ssum_ext. intros s _. apply Ssum_map.
Qed.

Lemma Ssum_ksum (R : poly) (s : mono * Z) (m : mono) :
  Ssum R (fun t => if mono_eq_dec (madd (fst s) (fst t)) m then snd s * snd t else 0)
  = snd s * ksum R (fun k => if mono_eq_dec (madd (fst s) k) m then 1 else 0).
Proof.
  induction R as [|t R IH]; [rewrite Ssum_nil; cbn [ksum]; ring|].
  rewrite Ssum_cons, IH. cbn [ksum]. cbv beta.
  destruct (mono_eq_dec (madd (fst s) (fst t)) m) as [E|E]; simpl; ring.
Qed.

Lemma pmul_pzero_r (p : Z) (f g : poly) : pzero p g -> pzero p (pmul f g).
Proof.
  intros H m. rewrite pcoef_pmul. apply Ssum_cg0. intros s _.
  rewrite Ssum_ksum. apply cg_zero_mul_r.
  apply (ksum_zero_keys mono_eq_dec p g). intros k _. apply H.
Qed.

Lemma pmul_app_r (f g h : poly) (m : mono) :
  pcoef (pmul f (g ++ h)) m = pcoef (pmul f g) m + pcoef (pmul f h) m.
Proof.
  rewrite !pcoef_pmul. rewrite <- Ssum_add. apply Ssum_ext. intros s _.
  apply Ssum_app.
Qed.

Lemma pmul_pneg_r (f g : poly) (m : mono) :
  pcoef (pmul f (pneg g)) m = - pcoef (pmul f g) m.
Proof.
  rewrite !pcoef_pmul. rewrite <- Ssum_opp. apply Ssum_ext. intros s _.
  unfold pneg. rewrite Ssum_map. rewrite <- Ssum_opp. apply Ssum_ext. intros t _.
  cbn [fst snd]. destruct (mono_eq_dec (madd (fst s) (fst t)) m); simpl; ring.
Qed.

Definition peq (p : Z) (f g : poly) : Prop := forall m, cg p (pcoef f m) (pcoef g m).

Lemma peq_refl (p : Z) (f : poly) : peq p f f.
Proof. intros m. apply cg_refl. Qed.

Lemma peq_sym (p : Z) (f g : poly) : peq p f g -> peq p g f.
Proof. intros H m. apply cg_sym. apply H. Qed.

Lemma peq_trans (p : Z) (f g h : poly) : peq p f g -> peq p g h -> peq p f h.
Proof. intros H1 H2 m. eapply cg_trans; [apply H1 | apply H2]. Qed.

Lemma peq_of_eq (p : Z) (f g : poly) : (forall m, pcoef f m = pcoef g m) -> peq p f g.
Proof. intros H m. apply cg_eq. apply H. Qed.

Lemma peq_pmul_r (p : Z) (f g g' : poly) : peq p g g' -> peq p (pmul f g) (pmul f g').
Proof.
  intros H m.
  assert (Hz : pzero p (g ++ pneg g')).
  { intros k. rewrite pcoef_app, pcoef_pneg. pose proof (H k) as Hk. unfold cg in *.
    replace (pcoef g k + - pcoef g' k - 0) with (pcoef g k - pcoef g' k) by ring. exact Hk. }
  pose proof (pmul_pzero_r p f _ Hz m) as Hm.
  rewrite pmul_app_r, pmul_pneg_r in Hm.
  unfold cg in *.
  replace (pcoef (pmul f g) m - pcoef (pmul f g') m)
    with (pcoef (pmul f g) m + - pcoef (pmul f g') m - 0) by ring.
  exact Hm.
Qed.

Lemma madd_comm (a b : mono) : madd a b = madd b a.
Proof.
  revert b. induction a as [|x a IH]; intros [|y b]; try reflexivity.
  simpl. rewrite (IH b). f_equal. lia.
Qed.

Lemma madd_assoc (a b c : mono) : madd a (madd b c) = madd (madd a b) c.
Proof.
  revert b c. induction a as [|x a IH]; intros b c; [reflexivity|].
  destruct b as [|y b]; [reflexivity|].
  destruct c as [|z c]; [reflexivity|].
  simpl. rewrite IH. f_equal. lia.
Qed.

Lemma madd_swap (a b c : mono) : madd a (madd b c) = madd b (madd a c).
Proof.
  rewrite (madd_assoc a b c), (madd_comm a b), <- (madd_assoc b a c); try reflexivity.
Qed.

Definition T3 (f g h : poly) (m : mono) : Z :=
  Ssum f (fun s => Ssum g (fun t => Ssum h (fun u =>
    if mono_eq_dec (madd (fst s) (madd (fst t) (fst u))) m then snd s * (snd t * snd u) else 0))).

Lemma ind_cong (a b m : mono) (c d : Z) : a = b -> c = d ->
  (if mono_eq_dec a m then c else 0) = (if mono_eq_dec b m then d else 0).
Proof. intros -> ->. reflexivity. Qed.

Lemma pmul_r_eq (f g h : poly) (m : mono) : pcoef (pmul f (pmul g h)) m = T3 f g h m.
Proof.
  rewrite pcoef_pmul. unfold T3. apply Ssum_ext. intros s _.
  rewrite Ssum_pmul. apply Ssum_ext. intros t _. apply Ssum_ext. intros u _.
  try cbn [fst snd]. reflexivity.
Qed.

Lemma pmul_l_eq (f g h : poly) (m : mono) : pcoef (pmul (pmul f g) h) m = T3 f g h m.
Proof.
  rewrite pcoef_pmul, Ssum_pmul. unfold T3. apply Ssum_ext. intros s _.
  apply Ssum_ext. intros t _. try cbn [fst snd]. apply Ssum_ext. intros u _. try cbn [fst snd].
  apply ind_cong; [symmetry; apply madd_assoc | ring].
Qed.

Lemma pmul_comm (f g : poly) (m : mono) : pcoef (pmul f g) m = pcoef (pmul g f) m.
Proof.
  rewrite !pcoef_pmul. rewrite (Ssum_swap f g). apply Ssum_ext. intros t _.
  apply Ssum_ext. intros s _.
  apply ind_cong; [apply madd_comm | ring].
Qed.

Lemma T3_swap12 (f g h : poly) (m : mono) : T3 f g h m = T3 g f h m.
Proof.
  unfold T3. rewrite (Ssum_swap f g). apply Ssum_ext. intros t _.
  apply Ssum_ext. intros s _. apply Ssum_ext. intros u _.
  apply ind_cong; [apply madd_swap | ring].
Qed.

Lemma pmul_swap (f g h : poly) (m : mono) :
  pcoef (pmul f (pmul g h)) m = pcoef (pmul g (pmul f h)) m.
Proof.
  etransitivity; [apply pmul_r_eq|]. etransitivity; [apply T3_swap12|]. symmetry. apply pmul_r_eq.
Qed.

Lemma pmul_assoc (f g h : poly) (m : mono) :
  pcoef (pmul (pmul f g) h) m = pcoef (pmul f (pmul g h)) m.
Proof. etransitivity; [apply pmul_l_eq|]. symmetry. apply pmul_r_eq. Qed.

Lemma pmul_nil_r (g : poly) : pmul g [] = [].
Proof. induction g as [|s g IH]; [reflexivity|]. unfold pmul in *. simpl. exact IH. Qed.

Lemma tinsp_get_aux (f : poly) : forall (t : tr) (m : mono),
  tget (fold_left (fun t a => tadd t (enc (fst a)) (snd a)) f t) (enc m) = tget t (enc m) + pcoef f m.
Proof.
  induction f as [|a f IH]; intros t m.
  - cbn [fold_left]. rewrite pcoef_nil. lia.
  - cbn [fold_left]. rewrite IH, tadd_enc, pcoef_cons.
    destruct (mono_eq_dec (fst a) m); simpl; lia.
Qed.

Definition tinsp (t : tr) (f : poly) : tr := fold_left (fun t a => tadd t (enc (fst a)) (snd a)) f t.

Lemma tinsp_get (f : poly) (t : tr) (m : mono) : tget (tinsp t f) (enc m) = tget t (enc m) + pcoef f m.
Proof. unfold tinsp. apply tinsp_get_aux. Qed.

Fixpoint drain (p : Z) (ms : list mono) (T : tr) (acc : poly) : tr * poly :=
  match ms with
  | [] => (T, acc)
  | m :: ms' =>
    let c := tget T (enc m) mod p in
    drain p ms' (tadd T (enc m) (- c)) ((m, c) :: acc)
  end.

Lemma drain_inv (p : Z) (ms : list mono) : forall (T : tr) (acc : poly) (m : mono),
  pcoef (snd (drain p ms T acc)) m + tget (fst (drain p ms T acc)) (enc m)
  = pcoef acc m + tget T (enc m).
Proof.
  induction ms as [|m0 ms IH]; intros T acc m.
  - cbn [drain fst snd]. lia.
  - cbn [drain]. rewrite IH. rewrite tadd_enc, pcoef_cons. cbn [fst snd].
    destruct (mono_eq_dec m0 m); simpl; lia.
Qed.

Lemma sub_mod_zero (p a : Z) : p <> 0 -> (a + - (a mod p)) mod p = 0.
Proof.
  intros Hp. apply (proj2 (Z.mod_divide _ _ Hp)).
  pose proof (cg_mod p a) as H. unfold cg in H.
  replace (a + - (a mod p)) with (- (a mod p - a)) by ring.
  exact (proj2 (Z.divide_opp_r p (a mod p - a)) H).
Qed.

Lemma drain_mod (p : Z) (Hp : p <> 0) (ms : list mono) : forall (T : tr) (acc : poly) (m : mono),
  (In m ms \/ tget T (enc m) mod p = 0) -> tget (fst (drain p ms T acc)) (enc m) mod p = 0.
Proof.
  induction ms as [|m0 ms IH]; intros T acc m H.
  - cbn [drain fst]. destruct H as [[]|H]; exact H.
  - cbn [drain]. apply IH. rewrite tadd_enc. destruct (mono_eq_dec m0 m) as [E|E]; simpl.
    + right. rewrite <- E. apply sub_mod_zero. exact Hp.
    + destruct H as [Hin|Hm].
      * destruct Hin as [Hin|Hin]; [exfalso; exact (E Hin) | left; exact Hin].
      * right. rewrite Z.add_0_r. exact Hm.
Qed.

Definition nz (t : mono * Z) : bool := negb (Z.eqb (snd t) 0).

Lemma pcoef_filter_nz (f : poly) (m : mono) : pcoef (filter nz f) m = pcoef f m.
Proof.
  induction f as [|t f IH]; [reflexivity|].
  cbn [filter]. destruct (nz t) eqn:E.
  - rewrite !pcoef_cons, IH; try reflexivity.
  - unfold nz in E. apply negb_false_iff in E. apply Z.eqb_eq in E.
    rewrite pcoef_cons, IH, E.
    destruct (mono_eq_dec (fst t) m); simpl; lia.
Qed.

Lemma pcoef_notin (f : poly) (m : mono) : ~ In m (map fst f) -> pcoef f m = 0.
Proof.
  induction f as [|t f IH]; intros H; [reflexivity|].
  rewrite pcoef_cons. cbn [map] in H.
  destruct (mono_eq_dec (fst t) m) as [E|E].
  - exfalso. apply H. left. exact E.
  - simpl. rewrite IH; [lia | intros Hin; apply H; right; exact Hin].
Qed.

Definition norm_poly (p : Z) (f : poly) : poly :=
  filter nz (snd (drain p (map fst f) (tinsp TL f) [])).

Lemma norm_poly_peq (p : Z) (Hp : p <> 0) (f : poly) : peq p (norm_poly p f) f.
Proof.
  intros m. unfold norm_poly. rewrite pcoef_filter_nz.
  pose proof (drain_inv p (map fst f) (tinsp TL f) [] m) as Hinv.
  assert (Hmod : tget (fst (drain p (map fst f) (tinsp TL f) [])) (enc m) mod p = 0).
  { apply drain_mod; [exact Hp|].
    destruct (in_dec mono_eq_dec m (map fst f)) as [Hin|Hout]; [left; exact Hin|right].
    rewrite tinsp_get. cbn [tget]. rewrite (pcoef_notin f m Hout). reflexivity. }
  rewrite pcoef_nil, tinsp_get in Hinv. cbn [tget] in Hinv.
  apply cg_zero_of_mod in Hmod.
  set (L := pcoef (snd (drain p (map fst f) (tinsp TL f) [])) m) in *.
  set (X := tget (fst (drain p (map fst f) (tinsp TL f) [])) (enc m)) in *.
  unfold cg in *.
  replace (L - pcoef f m) with (- (X - 0)) by lia.
  exact (proj2 (Z.divide_opp_r p (X - 0)) Hmod).
Qed.

Fixpoint tri (k : nat) : nat := match k with O => O | S k' => (S k' + tri k')%nat end.

Fixpoint zipapp (a b : list poly) : list poly :=
  match a, b with
  | x :: a', y :: b' => (x ++ y) :: zipapp a' b'
  | _, _ => []
  end.

Fixpoint chunk (np n : nat) (l : list poly) : list (list poly) :=
  match n with
  | O => []
  | S n' => firstn np l :: chunk np n' (skipn np l)
  end.

Fixpoint stage1 (n : nat) (ks : list nat) (bls : list (list poly)) (acc : list poly) : list poly :=
  match ks, bls with
  | k :: ks', bl :: bls' => stage1 n ks' bls' (zipapp acc (map (fun c => pmul c (var n k)) bl))
  | _, _ => acc
  end.

Definition hflat (hs : list (poly * poly)) : poly := flat_map (fun gh => pmul (fst gh) (snd gh)) hs.

Fixpoint hlist (p : Z) (n : nat) (G : list poly) (Bs : list poly) : list (poly * poly) :=
  match G with
  | [] => []
  | g :: G' =>
    (g, norm_poly p (combo (map (fun h => pmul h (one_poly n)) G) (firstn (length G) Bs)))
      :: hlist p n G' (skipn (length G) Bs)
  end.

Fixpoint hfold (t : tr) (hs : list (poly * poly)) : tr :=
  match hs with
  | [] => t
  | gh :: r => hfold (tmul (-1) t (fst gh) (snd gh)) r
  end.

Lemma stage1_cons (n k : nat) (ks : list nat) (bl : list poly) (bls : list (list poly)) (acc : list poly) :
  stage1 n (k :: ks) (bl :: bls) acc = stage1 n ks bls (zipapp acc (map (fun c => pmul c (var n k)) bl)).
Proof. reflexivity. Qed.

Lemma hflat_cons (gh : poly * poly) (r : list (poly * poly)) :
  hflat (gh :: r) = pmul (fst gh) (snd gh) ++ hflat r.
Proof. reflexivity. Qed.

Lemma hlist_cons (p : Z) (n : nat) (g : poly) (G : list poly) (Bs : list poly) :
  hlist p n (g :: G) Bs =
  (g, norm_poly p (combo (map (fun h => pmul h (one_poly n)) (g :: G)) (firstn (length (g :: G)) Bs)))
    :: hlist p n G (skipn (length (g :: G)) Bs).
Proof. reflexivity. Qed.

Lemma mset_aux_one (n : nat) (G : list poly) :
  mset_aux pmul (fun _ : list poly => [one_poly n]) G = map (fun h => pmul h (one_poly n)) G.
Proof.
  induction G as [|g G IH]; [reflexivity|].
  cbn [mset_aux map]. rewrite IH; try reflexivity.
Qed.

Lemma products1_eq (n : nat) (G : list poly) : products n G 1 = map (fun h => pmul h (one_poly n)) G.
Proof. exact (mset_aux_one n G). Qed.

Lemma products2_cons (n : nat) (g : poly) (G : list poly) :
  products n (g :: G) 2 = map (pmul g) (products n (g :: G) 1) ++ products n G 2.
Proof. reflexivity. Qed.

Lemma products2_len (n : nat) (G : list poly) : length (products n G 2) = tri (length G).
Proof.
  induction G as [|g G IH]; [reflexivity|].
  rewrite products2_cons, length_app, length_map, products1_eq, length_map, IH; try reflexivity.
Qed.

Lemma m_products_len (n : nat) (G : list poly) :
  length (m_products n G 2) = (n * tri (length G))%nat.
Proof.
  unfold m_products.
  assert (H : forall ks : list nat,
    length (flat_map (fun k => map (pmul (var n k)) (products n G 2)) ks) = (length ks * tri (length G))%nat).
  { induction ks as [|k ks IH]; [reflexivity|].
    cbn [flat_map]. rewrite length_app, length_map, IH, products2_len; simpl; lia. }
  rewrite H, length_seq; try reflexivity.
Qed.

Lemma combo_app (cs1 gs1 cs2 gs2 : list poly) : length cs1 = length gs1 ->
  combo (cs1 ++ cs2) (gs1 ++ gs2) = combo cs1 gs1 ++ combo cs2 gs2.
Proof.
  revert gs1. induction cs1 as [|c cs1 IH]; intros gs1 H; destruct gs1 as [|g gs1]; try discriminate H.
  - reflexivity.
  - cbn [app combo]. rewrite IH by (injection H as H; exact H). apply app_assoc.
Qed.

Lemma pmul_app_l (f f' g : poly) : pmul (f ++ f') g = pmul f g ++ pmul f' g.
Proof. unfold pmul. apply flat_map_app. Qed.

Lemma combo_zipapp (m : mono) (PR : list poly) : forall (a b : list poly),
  length a = length PR -> length b = length PR ->
  pcoef (combo (zipapp a b) PR) m = pcoef (combo a PR) m + pcoef (combo b PR) m.
Proof.
  induction PR as [|P PR IH]; intros a b Ha Hb; destruct a as [|x a]; destruct b as [|y b];
    try discriminate Ha; try discriminate Hb.
  - reflexivity.
  - cbn [zipapp combo]. rewrite !pcoef_app, pmul_app_l, pcoef_app.
    rewrite IH by (first [injection Ha as Ha; exact Ha | injection Hb as Hb; exact Hb]).
    ring.
Qed.

Lemma combo_assoc_map (v : poly) (m : mono) : forall (bl PR : list poly),
  pcoef (combo (map (fun c => pmul c v) bl) PR) m = pcoef (combo bl (map (pmul v) PR)) m.
Proof.
  induction bl as [|c bl IH]; intros PR; [reflexivity|].
  destruct PR as [|P PR]; [reflexivity|].
  cbn [map combo]. rewrite !pcoef_app, IH, pmul_assoc; try reflexivity.
Qed.

Lemma zipapp_len (a b : list poly) : length a = length b -> length (zipapp a b) = length a.
Proof.
  revert b. induction a as [|x a IH]; intros b H; destruct b as [|y b].
  - reflexivity.
  - discriminate H.
  - discriminate H.
  - cbn [zipapp length]. f_equal. apply IH. injection H as H. exact H.
Qed.

Lemma combo_repeat_nil (k : nat) (m : mono) : forall PR : list poly,
  pcoef (combo (repeat [] k) PR) m = 0.
Proof.
  induction k as [|k IH]; intros PR; [reflexivity|].
  destruct PR as [|P PR]; [reflexivity|].
  cbn [repeat combo]. rewrite pcoef_app, IH.
  replace (pmul [] P) with (@nil (mono * Z)) by reflexivity.
  rewrite pcoef_nil. lia.
Qed.

Lemma chunk_concat (np : nat) : forall (n : nat) (l : list poly),
  length l = (n * np)%nat -> concat (chunk np n l) = l.
Proof.
  induction n as [|n IH]; intros l H.
  - cbn [chunk concat]. destruct l; [reflexivity | simpl in H; discriminate H].
  - cbn [chunk concat]. rewrite Nat.mul_succ_l in H. rewrite IH.
    + apply firstn_skipn.
    + rewrite length_skipn. lia.
Qed.

Lemma chunk_len (np : nat) : forall (n : nat) (l : list poly), length l = (n * np)%nat ->
  length (chunk np n l) = n /\ (forall bl, In bl (chunk np n l) -> length bl = np).
Proof.
  induction n as [|n IH]; intros l H.
  - split; [reflexivity | intros bl Hbl; destruct Hbl].
  - cbn [chunk]. rewrite Nat.mul_succ_l in H.
    assert (Hl : length (skipn np l) = (n * np)%nat) by (rewrite length_skipn; lia).
    destruct (IH _ Hl) as [H1 H2]. split.
    + cbn [length]. f_equal. exact H1.
    + intros bl [<-|Hbl].
      * rewrite length_firstn. lia.
      * exact (H2 bl Hbl).
Qed.

Lemma stage1_len (n : nat) : forall (ks : list nat) (bls : list (list poly)) (acc : list poly),
  (forall bl, In bl bls -> length bl = length acc) -> length (stage1 n ks bls acc) = length acc.
Proof.
  induction ks as [|k ks IH]; intros bls acc H; destruct bls as [|bl bls]; try reflexivity.
  rewrite stage1_cons.
  assert (HA : length (map (fun c => pmul c (var n k)) bl) = length acc)
    by (rewrite length_map; apply H; left; reflexivity).
  assert (Hz : length (zipapp acc (map (fun c => pmul c (var n k)) bl)) = length acc)
    by (rewrite zipapp_len; [reflexivity | rewrite HA; reflexivity]).
  rewrite IH.
  - exact Hz.
  - intros bl' Hin. rewrite Hz. apply H. right. exact Hin.
Qed.

Lemma stage1_spec (n : nat) (G : list poly) (m : mono) :
  forall (ks : list nat) (bls : list (list poly)) (acc : list poly),
    length ks = length bls ->
    (forall bl, In bl bls -> length bl = tri (length G)) ->
    length acc = tri (length G) ->
    pcoef (combo (stage1 n ks bls acc) (products n G 2)) m
    = pcoef (combo acc (products n G 2)) m
      + pcoef (combo (concat bls) (flat_map (fun k => map (pmul (var n k)) (products n G 2)) ks)) m.
Proof.
  intros ks. induction ks as [|k ks IH]; intros bls acc Hl Hbl Hacc; destruct bls as [|bl bls].
  - cbn [stage1 concat flat_map combo]. rewrite pcoef_nil. lia.
  - discriminate Hl.
  - discriminate Hl.
  - rewrite stage1_cons.
    assert (Hbl1 : length bl = tri (length G)) by (apply Hbl; left; reflexivity).
    assert (HPR : length (products n G 2) = tri (length G)) by apply products2_len.
    assert (HA : length (map (fun c => pmul c (var n k)) bl) = tri (length G))
      by (rewrite length_map; exact Hbl1).
    assert (Hz : length (zipapp acc (map (fun c => pmul c (var n k)) bl)) = tri (length G)).
    { rewrite zipapp_len; [exact Hacc | rewrite HA; exact Hacc]. }
    assert (H1 : length ks = length bls) by (injection Hl as Hl; exact Hl).
    assert (H2 : forall bl', In bl' bls -> length bl' = tri (length G))
      by (intros bl' Hin; apply Hbl; right; exact Hin).
    rewrite (IH bls _ H1 H2 Hz).
    rewrite combo_zipapp; [|rewrite HPR; exact Hacc|rewrite HPR; exact HA].
    rewrite combo_assoc_map.
    cbn [concat flat_map].
    rewrite combo_app; [|rewrite length_map; rewrite HPR; exact Hbl1].
    rewrite pcoef_app. ring.
Qed.

Lemma horner_head (p : Z) (Hp : p <> 0) (g : poly) : forall (Bc Xs : list poly),
  length Bc = length Xs ->
  peq p (combo Bc (map (pmul g) Xs)) (pmul g (combo Xs (map (norm_poly p) Bc))).
Proof.
  induction Bc as [|B Bc IH]; intros Xs H; destruct Xs as [|X Xs]; try discriminate H.
  - intros m. cbn [map combo]. rewrite pmul_nil_r. apply cg_refl.
  - intros m. cbn [map combo]. rewrite pmul_app_r, !pcoef_app.
    apply cg_add.
    + eapply cg_trans.
      * apply cg_eq. apply pmul_swap.
      * apply (peq_pmul_r p g (pmul B X) (pmul X (norm_poly p B))).
        eapply peq_trans; [apply peq_of_eq; intros m'; apply pmul_comm|].
        apply peq_pmul_r. apply peq_sym. apply norm_poly_peq. exact Hp.
    + apply (IH Xs). injection H as H. exact H.
Qed.

Lemma horner (p : Z) (Hp : p <> 0) (n : nat) : forall (G Bc : list poly) (m : mono),
  length Bc = tri (length G) ->
  cg p (pcoef (combo Bc (products n G 2)) m)
       (pcoef (hflat (hlist p n G (map (norm_poly p) Bc))) m).
Proof.
  induction G as [|g G IH]; intros Bc m H.
  - destruct Bc as [|B Bc]; [apply cg_refl | discriminate H].
  - cbn [length tri] in H.
    assert (Hl1 : length (firstn (length (g :: G)) Bc) = S (length G)) by (rewrite length_firstn; cbn [length]; lia).
    assert (Hl2 : length (skipn (length (g :: G)) Bc) = tri (length G)) by (rewrite length_skipn; cbn [length]; lia).
    assert (HX : length (firstn (length (g :: G)) Bc) = length (map (fun h => pmul h (one_poly n)) (g :: G)))
      by (rewrite length_map; cbn [length]; exact Hl1).
    assert (E : combo Bc (products n (g :: G) 2)
      = combo (firstn (length (g :: G)) Bc) (map (pmul g) (map (fun h => pmul h (one_poly n)) (g :: G)))
        ++ combo (skipn (length (g :: G)) Bc) (products n G 2)).
    { rewrite products2_cons, products1_eq.
      rewrite <- combo_app by (rewrite length_map; exact HX).
      now rewrite firstn_skipn. }
    rewrite E, hlist_cons, hflat_cons, !pcoef_app. cbn [fst snd].
    rewrite firstn_map, skipn_map.
    apply cg_add.
    + eapply cg_trans.
      * apply (horner_head p Hp g (firstn (length (g :: G)) Bc) (map (fun h => pmul h (one_poly n)) (g :: G)) HX).
      * apply cg_sym. apply (peq_pmul_r p g). apply norm_poly_peq. exact Hp.
    + apply IH. exact Hl2.
Qed.

Lemma hfold_get (hs : list (poly * poly)) : forall (t : tr) (m : mono),
  tget (hfold t hs) (enc m) = tget t (enc m) + (-1) * pcoef (hflat hs) m.
Proof.
  induction hs as [|gh hs IH]; intros t m.
  - cbn [hfold]. unfold hflat. cbn [flat_map]. rewrite pcoef_nil. lia.
  - cbn [hfold]. rewrite IH, tmul_get, hflat_cons, pcoef_app. lia.
Qed.

Lemma master (p : Z) (Hp : p <> 0) (n : nat) (J G cofs : list poly) (m : mono) :
  length cofs = (length J + n * tri (length G))%nat ->
  cg p (pcoef (combo cofs (J ++ m_products n G 2)) m)
       (pcoef (combo (firstn (length J) cofs) J) m +
        pcoef (hflat (hlist p n G (map (norm_poly p)
          (stage1 n (seq 0 n) (chunk (tri (length G)) n (skipn (length J) cofs))
             (repeat [] (tri (length G))))))) m).
Proof.
  intros H.
  assert (HcJ : length (firstn (length J) cofs) = length J) by (rewrite length_firstn; lia).
  assert (HcM : length (skipn (length J) cofs) = (n * tri (length G))%nat) by (rewrite length_skipn; lia).
  assert (Hch := chunk_len (tri (length G)) n _ HcM).
  assert (Hk : length (seq 0 n) = length (chunk (tri (length G)) n (skipn (length J) cofs)))
    by (rewrite length_seq; symmetry; exact (proj1 Hch)).
  assert (Hr : length (repeat ([] : poly) (tri (length G))) = tri (length G)) by apply repeat_length.
  assert (Hs := stage1_spec n G m (seq 0 n) (chunk (tri (length G)) n (skipn (length J) cofs))
    (repeat [] (tri (length G))) Hk (proj2 Hch) Hr).
  rewrite chunk_concat in Hs by exact HcM.
  rewrite combo_repeat_nil in Hs.
  assert (HBc : length (stage1 n (seq 0 n) (chunk (tri (length G)) n (skipn (length J) cofs))
    (repeat [] (tri (length G)))) = tri (length G)).
  { etransitivity; [apply stage1_len|exact Hr]. intros bl Hbl. rewrite repeat_length. exact (proj2 Hch bl Hbl). }
  pose proof (horner p Hp n G _ m HBc) as Hh.
  rewrite Hs, Z.add_0_l in Hh.
  assert (Hcc : cofs = firstn (length J) cofs ++ skipn (length J) cofs)
    by (symmetry; apply (firstn_skipn (A := poly))).
  replace (combo cofs (J ++ m_products n G 2))
    with (combo (firstn (length J) cofs ++ skipn (length J) cofs) (J ++ m_products n G 2))
    by (f_equal; symmetry; exact Hcc).
  rewrite combo_app by exact HcJ.
  rewrite pcoef_app. apply cg_add; [apply cg_refl|].
  unfold m_products. exact Hh.
Qed.

Lemma cg_combine (p A B C D T0 : Z) : T0 = 0 ->
  cg p (T0 + 1 * A + -1 * B + -1 * C) 0 -> cg p D (B + C) -> cg p (A + - D) 0.
Proof.
  intros HT H1 H2. subst T0. unfold cg in *.
  replace (A + - D - 0) with ((0 + 1 * A + -1 * B + -1 * C - 0) - (D - (B + C))) by ring.
  apply Z.divide_sub_r; assumption.
Qed.

Definition check_factored (p : Z) (n : nat) (J G : list poly) (q : list (Z * list nat)) (c : kcert) : bool :=
  Z.ltb 0 p &&
  negb (Z.eqb (const_coef (k_u c) mod p) 0) &&
  wf_b n (k_u c) && forallb (wf_b n) (k_cofs c) &&
  Nat.eqb (length (k_cofs c)) (length J + n * tri (length G)) &&
  tall p (hfold (tcombo (-1) (tmul 1 TL (k_u c) (subst_q n G q)) (firstn (length J) (k_cofs c)) J)
    (hlist p n G (map (norm_poly p)
      (stage1 n (seq 0 n) (chunk (tri (length G)) n (skipn (length J) (k_cofs c)))
        (repeat [] (tri (length G))))))).

(** An accepted certificate gives the unit and cofactors of [in_local_ideal]: [master] equates the Horner grouping
    with the plain sum of cofactor products modulo p, and [tall_sound] turns the passed coefficient test into
    that congruence. *)
Theorem check_factored_sound (p : Z) (n : nat) (J G : list poly) (q : list (Z * list nat)) (c : kcert) :
  check_factored p n J G q c = true ->
  in_local_ideal p n (J ++ m_products n G 2) (subst_q n G q).
Proof.
  unfold check_factored. intros H.
  repeat (apply andb_true_iff in H as [H ?]).
  match goal with
  | [ Hp : Z.ltb 0 p = true, Hu : negb (Z.eqb (const_coef (k_u c) mod p) 0) = true,
      Hw : wf_b n (k_u c) = true, Hc : forallb (wf_b n) (k_cofs c) = true,
      Hl : Nat.eqb _ _ = true, Ht : tall _ _ = true |- _ ] =>
    assert (Hp0 : p <> 0) by (apply Z.ltb_lt in Hp; lia);
    apply Nat.eqb_eq in Hl;
    exists (k_u c), (k_cofs c);
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
      pose proof (master p Hp0 n J G (k_cofs c) m Hl) as Hm;
      exact (cg_combine p _ _ _ _ _ eq_refl E Hm) ]
  end.
Qed.

Definition check_data_factored (p : Z) (n : nat) (J G : list poly) (q : list (Z * list nat))
  (b : N) (dat : kdata) : bool :=
  check_factored p n J G q (decode_cert b n (length J + n * tri (length G)) dat).

(** The data form reduces to [check_factored_sound]: [check_data_factored] is [check_factored] on the certificate
    that [decode_cert] reads from the packed data. *)
Theorem check_data_factored_sound (p : Z) (n : nat) (J G : list poly) (q : list (Z * list nat))
  (b : N) (dat : kdata) :
  check_data_factored p n J G q b dat = true ->
  in_local_ideal p n (J ++ m_products n G 2) (subst_q n G q).
Proof. unfold check_data_factored. apply check_factored_sound. Qed.

Lemma toy_accepted_f : check_factored 7 1 toy_J toy_G toy_q toy_cert = true.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_coefficient_rejected_f :
  check_factored 7 1 toy_J toy_G toy_q
    (mk_kcert [([0%nat], 1); ([1%nat], 1)] [ [([0%nat], 1)]; [([0%nat], 2)] ]) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_exponent_rejected_f :
  check_factored 7 1 toy_J toy_G toy_q
    (mk_kcert [([0%nat], 1); ([1%nat], 1)] [ [([0%nat], 1)]; [([1%nat], 1)] ]) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_unit_rejected_f :
  check_factored 7 1 toy_J toy_G toy_q
    (mk_kcert [([1%nat], 1)] [ [([0%nat], 1)]; [([0%nat], 1)] ]) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_count_rejected_f :
  check_factored 7 1 toy_J toy_G toy_q
    (mk_kcert [([0%nat], 1); ([1%nat], 1)] [ [([0%nat], 1)] ]) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_data_accepted_f : check_data_factored 7 1 toy_J toy_G toy_q 15 (toy_data 1) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_data_rejected_f : check_data_factored 7 1 toy_J toy_G toy_q 15 (toy_data 2) = false.
Proof. vm_compute. reflexivity. Qed.

Theorem toy_in_ideal_f :
  in_local_ideal 7 1 (toy_J ++ m_products 1 toy_G 2) (subst_q 1 toy_G toy_q).
Proof. exact (check_factored_sound _ _ _ _ _ _ toy_accepted_f). Qed.

Print Assumptions toy_in_ideal_f.
Print Assumptions check_data_factored_sound.
